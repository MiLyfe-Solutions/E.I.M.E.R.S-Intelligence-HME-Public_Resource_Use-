import V185TrunkScan20Chunk078

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_481457 : List Nat := [1, 2, 2, 5, 2, 1, 1, 3, 3]
def baseStart_481457 : Nat := 118140960795 + 481457 * 2 ^ 59
def prefixEnd_481457 : Nat := 4983230072969 + 3 ^ 40 * 481457 * 2
def baseEnd_481457 : Nat := 219750093752736027531845

theorem tailTrace_481457 : CollatzResearch.WordTrace tailWord_481457 prefixEnd_481457 219750093752736027531845 := by
  unfold tailWord_481457
  simp only [CollatzResearch.WordTrace]
  refine ⟨17560179416770990154338625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11706786277847326769559083 17560179416770990154338625)
  ·
    refine ⟨13170134562578242615753969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17560179416770990154338625 13170134562578242615753969)
    ·
      refine ⟨9877600921933681961815477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13170134562578242615753969 9877600921933681961815477)
      ·
        refine ⟨926025086431282683920201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9877600921933681961815477 926025086431282683920201)
        ·
          refine ⟨694518814823462012940151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 926025086431282683920201 694518814823462012940151)
          ·
            refine ⟨1041778222235193019410227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694518814823462012940151 1041778222235193019410227)
            ·
              refine ⟨1562667333352789529115341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041778222235193019410227 1562667333352789529115341)
              ·
                refine ⟨586000250007296073418253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1562667333352789529115341 586000250007296073418253)
                ·
                  refine ⟨219750093752736027531845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586000250007296073418253 219750093752736027531845)
                  ·
                    rfl

theorem cell20_481457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_481457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481457 prefixEnd_481457 := by exact prefixLift 481457
  have htrace : WordTrace (prefixWord ++ tailWord_481457) baseStart_481457 baseEnd_481457 := by
    simpa [prefixWord, tailWord_481457, baseEnd_481457] using wordTrace_append hprefix tailTrace_481457
  have hstable : (prefixWord ++ tailWord_481457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481457).length < 2 ^ (prefixWord ++ tailWord_481457).sum := by decide
  have hdescent : baseEnd_481457 < baseStart_481457 := by decide
  rcases family_descends (prefixWord ++ tailWord_481457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481499 : List Nat := [1, 1, 1, 1, 1, 1, 1, 10, 3]
def baseStart_481499 : Nat := 118140960795 + 481499 * 2 ^ 59
def prefixEnd_481499 : Nat := 4983230072969 + 3 ^ 40 * 481499 * 2
def baseEnd_481499 : Nat := 219769263697170548131673

theorem tailTrace_481499 : CollatzResearch.WordTrace tailWord_481499 prefixEnd_481499 219769263697170548131673 := by
  unfold tailWord_481499
  simp only [CollatzResearch.WordTrace]
  refine ⟨17561711282618831327367551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11707807521745887551578367 17561711282618831327367551)
  ·
    refine ⟨26342566923928246991051327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17561711282618831327367551 26342566923928246991051327)
    ·
      refine ⟨39513850385892370486576991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26342566923928246991051327 39513850385892370486576991)
      ·
        refine ⟨59270775578838555729865487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39513850385892370486576991 59270775578838555729865487)
        ·
          refine ⟨88906163368257833594798231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59270775578838555729865487 88906163368257833594798231)
          ·
            refine ⟨133359245052386750392197347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88906163368257833594798231 133359245052386750392197347)
            ·
              refine ⟨200038867578580125588296021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133359245052386750392197347 200038867578580125588296021)
              ·
                refine ⟨586051369859121461684461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 200038867578580125588296021 586051369859121461684461)
                ·
                  refine ⟨219769263697170548131673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586051369859121461684461 219769263697170548131673)
                  ·
                    rfl

theorem cell20_481499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 3].length) (baseStart_481499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481499 prefixEnd_481499 := by exact prefixLift 481499
  have htrace : WordTrace (prefixWord ++ tailWord_481499) baseStart_481499 baseEnd_481499 := by
    simpa [prefixWord, tailWord_481499, baseEnd_481499] using wordTrace_append hprefix tailTrace_481499
  have hstable : (prefixWord ++ tailWord_481499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481499).length < 2 ^ (prefixWord ++ tailWord_481499).sum := by decide
  have hdescent : baseEnd_481499 < baseStart_481499 := by decide
  rcases family_descends (prefixWord ++ tailWord_481499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481509 : List Nat := [1, 3, 1, 4, 2, 3, 1, 5]
def baseStart_481509 : Nat := 118140960795 + 481509 * 2 ^ 59
def prefixEnd_481509 : Nat := 4983230072969 + 3 ^ 40 * 481509 * 2
def baseEnd_481509 : Nat := 73257942656551652599433

theorem tailTrace_481509 : CollatzResearch.WordTrace tailWord_481509 prefixEnd_481509 73257942656551652599433 := by
  unfold tailWord_481509
  simp only [CollatzResearch.WordTrace]
  refine ⟨17562076012582603035231581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11708050675055068690154387 17562076012582603035231581)
  ·
    refine ⟨6585778504718476138211843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17562076012582603035231581 6585778504718476138211843)
    ·
      refine ⟨9878667757077714207317765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6585778504718476138211843 9878667757077714207317765)
      ·
        refine ⟨1852250204452071413872081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9878667757077714207317765 1852250204452071413872081)
        ·
          refine ⟨1389187653339053560404061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1852250204452071413872081 1389187653339053560404061)
          ·
            refine ⟨520945370002145085151523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1389187653339053560404061 520945370002145085151523)
            ·
              refine ⟨781418055003217627727285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520945370002145085151523 781418055003217627727285)
              ·
                refine ⟨73257942656551652599433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 781418055003217627727285 73257942656551652599433)
                ·
                  rfl

theorem cell20_481509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 5].length) (baseStart_481509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481509 prefixEnd_481509 := by exact prefixLift 481509
  have htrace : WordTrace (prefixWord ++ tailWord_481509) baseStart_481509 baseEnd_481509 := by
    simpa [prefixWord, tailWord_481509, baseEnd_481509] using wordTrace_append hprefix tailTrace_481509
  have hstable : (prefixWord ++ tailWord_481509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481509).length < 2 ^ (prefixWord ++ tailWord_481509).sum := by decide
  have hdescent : baseEnd_481509 < baseStart_481509 := by decide
  rcases family_descends (prefixWord ++ tailWord_481509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481537 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 5]
def baseStart_481537 : Nat := 118140960795 + 481537 * 2 ^ 59
def prefixEnd_481537 : Nat := 4983230072969 + 3 ^ 40 * 481537 * 2
def baseEnd_481537 : Nat := 219786607932611304864851

theorem tailTrace_481537 : CollatzResearch.WordTrace tailWord_481537 prefixEnd_481537 219786607932611304864851 := by
  unfold tailWord_481537
  simp only [CollatzResearch.WordTrace]
  refine ⟨17563097256481163817250865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11708731504320775878167243 17563097256481163817250865)
  ·
    refine ⟨13172322942360872862938149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17563097256481163817250865 13172322942360872862938149)
    ·
      refine ⟨2469810551692663661800903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13172322942360872862938149 2469810551692663661800903)
      ·
        refine ⟨3704715827538995492701355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2469810551692663661800903 3704715827538995492701355)
        ·
          refine ⟨5557073741308493239052033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3704715827538995492701355 5557073741308493239052033)
          ·
            refine ⟨4167805305981369929289025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5557073741308493239052033 4167805305981369929289025)
            ·
              refine ⟨3125853979486027446966769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4167805305981369929289025 3125853979486027446966769)
              ·
                refine ⟨2344390484614520585225077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125853979486027446966769 2344390484614520585225077)
                ·
                  refine ⟨219786607932611304864851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2344390484614520585225077 219786607932611304864851)
                  ·
                    rfl

theorem cell20_481537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_481537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481537 prefixEnd_481537 := by exact prefixLift 481537
  have htrace : WordTrace (prefixWord ++ tailWord_481537) baseStart_481537 baseEnd_481537 := by
    simpa [prefixWord, tailWord_481537, baseEnd_481537] using wordTrace_append hprefix tailTrace_481537
  have hstable : (prefixWord ++ tailWord_481537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481537).length < 2 ^ (prefixWord ++ tailWord_481537).sum := by decide
  have hdescent : baseEnd_481537 < baseStart_481537 := by decide
  rcases family_descends (prefixWord ++ tailWord_481537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481581 : List Nat := [1, 5, 3, 1, 2, 2, 2, 4]
def baseStart_481581 : Nat := 118140960795 + 481581 * 2 ^ 59
def prefixEnd_481581 : Nat := 4983230072969 + 3 ^ 40 * 481581 * 2
def baseEnd_481581 : Nat := 73268896910514235799335

theorem tailTrace_481581 : CollatzResearch.WordTrace tailWord_481581 prefixEnd_481581 73268896910514235799335 := by
  unfold tailWord_481581
  simp only [CollatzResearch.WordTrace]
  refine ⟨17564702068321759331852597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11709801378881172887901731 17564702068321759331852597)
  ·
    refine ⟨1646690818905164937361181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17564702068321759331852597 1646690818905164937361181)
    ·
      refine ⟨617509057089436851510443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1646690818905164937361181 617509057089436851510443)
      ·
        refine ⟨926263585634155277265665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617509057089436851510443 926263585634155277265665)
        ·
          refine ⟨694697689225616457949249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 926263585634155277265665 694697689225616457949249)
          ·
            refine ⟨521023266919212343461937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 694697689225616457949249 521023266919212343461937)
            ·
              refine ⟨390767450189409257596453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 521023266919212343461937 390767450189409257596453)
              ·
                refine ⟨73268896910514235799335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 390767450189409257596453 73268896910514235799335)
                ·
                  rfl

theorem cell20_481581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 4].length) (baseStart_481581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481581 prefixEnd_481581 := by exact prefixLift 481581
  have htrace : WordTrace (prefixWord ++ tailWord_481581) baseStart_481581 baseEnd_481581 := by
    simpa [prefixWord, tailWord_481581, baseEnd_481581] using wordTrace_append hprefix tailTrace_481581
  have hstable : (prefixWord ++ tailWord_481581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481581).length < 2 ^ (prefixWord ++ tailWord_481581).sum := by decide
  have hdescent : baseEnd_481581 < baseStart_481581 := by decide
  rcases family_descends (prefixWord ++ tailWord_481581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481668 : List Nat := [2, 3, 2, 1, 1, 2, 4, 2, 3]
def baseStart_481668 : Nat := 118140960795 + 481668 * 2 ^ 59
def prefixEnd_481668 : Nat := 4983230072969 + 3 ^ 40 * 481668 * 2
def baseEnd_481668 : Nat := 219846399902157071497649

theorem tailTrace_481668 : CollatzResearch.WordTrace tailWord_481668 prefixEnd_481668 219846399902157071497649 := by
  unfold tailWord_481668
  simp only [CollatzResearch.WordTrace]
  refine ⟨8783937609503286595134829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11711916812671048793513105 8783937609503286595134829)
  ·
    refine ⟨3293976603563732473175561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8783937609503286595134829 3293976603563732473175561)
    ·
      refine ⟨2470482452672799354881671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3293976603563732473175561 2470482452672799354881671)
      ·
        refine ⟨3705723679009199032322507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2470482452672799354881671 3705723679009199032322507)
        ·
          refine ⟨5558585518513798548483761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3705723679009199032322507 5558585518513798548483761)
          ·
            refine ⟨4168939138885348911362821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5558585518513798548483761 4168939138885348911362821)
            ·
              refine ⟨781676088541002920880529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4168939138885348911362821 781676088541002920880529)
              ·
                refine ⟨586257066405752190660397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 781676088541002920880529 586257066405752190660397)
                ·
                  refine ⟨219846399902157071497649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586257066405752190660397 219846399902157071497649)
                  ·
                    rfl

theorem cell20_481668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_481668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481668 prefixEnd_481668 := by exact prefixLift 481668
  have htrace : WordTrace (prefixWord ++ tailWord_481668) baseStart_481668 baseEnd_481668 := by
    simpa [prefixWord, tailWord_481668, baseEnd_481668] using wordTrace_append hprefix tailTrace_481668
  have hstable : (prefixWord ++ tailWord_481668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481668).length < 2 ^ (prefixWord ++ tailWord_481668).sum := by decide
  have hdescent : baseEnd_481668 < baseStart_481668 := by decide
  rcases family_descends (prefixWord ++ tailWord_481668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481689 : List Nat := [1, 2, 1, 2, 1, 4, 1, 5, 3]
def baseStart_481689 : Nat := 118140960795 + 481689 * 2 ^ 59
def prefixEnd_481689 : Nat := 4983230072969 + 3 ^ 40 * 481689 * 2
def baseEnd_481689 : Nat := 219855984874374331797563

theorem tailTrace_481689 : CollatzResearch.WordTrace tailWord_481689 prefixEnd_481689 219855984874374331797563 := by
  unfold tailWord_481689
  simp only [CollatzResearch.WordTrace]
  refine ⟨17568641151930493776784121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11712427434620329184522747 17568641151930493776784121)
  ·
    refine ⟨13176480863947870332588091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17568641151930493776784121 13176480863947870332588091)
    ·
      refine ⟨19764721295921805498882137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13176480863947870332588091 19764721295921805498882137)
      ·
        refine ⟨14823540971941354124161603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19764721295921805498882137 14823540971941354124161603)
        ·
          refine ⟨22235311457912031186242405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14823540971941354124161603 22235311457912031186242405)
          ·
            refine ⟨4169120898358505847420451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22235311457912031186242405 4169120898358505847420451)
            ·
              refine ⟨6253681347537758771130677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4169120898358505847420451 6253681347537758771130677)
              ·
                refine ⟨586282626331664884793501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6253681347537758771130677 586282626331664884793501)
                ·
                  refine ⟨219855984874374331797563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586282626331664884793501 219855984874374331797563)
                  ·
                    rfl

theorem cell20_481689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_481689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481689 prefixEnd_481689 := by exact prefixLift 481689
  have htrace : WordTrace (prefixWord ++ tailWord_481689) baseStart_481689 baseEnd_481689 := by
    simpa [prefixWord, tailWord_481689, baseEnd_481689] using wordTrace_append hprefix tailTrace_481689
  have hstable : (prefixWord ++ tailWord_481689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481689).length < 2 ^ (prefixWord ++ tailWord_481689).sum := by decide
  have hdescent : baseEnd_481689 < baseStart_481689 := by decide
  rcases family_descends (prefixWord ++ tailWord_481689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481696 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 6]
def baseStart_481696 : Nat := 118140960795 + 481696 * 2 ^ 59
def prefixEnd_481696 : Nat := 4983230072969 + 3 ^ 40 * 481696 * 2
def baseEnd_481696 : Nat := 219859179865113418564201

theorem tailTrace_481696 : CollatzResearch.WordTrace tailWord_481696 prefixEnd_481696 219859179865113418564201 := by
  unfold tailWord_481696
  simp only [CollatzResearch.WordTrace]
  refine ⟨8784448231452566986144471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11712597641936755981525961 8784448231452566986144471)
  ·
    refine ⟨13176672347178850479216707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8784448231452566986144471 13176672347178850479216707)
    ·
      refine ⟨19765008520768275718825061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13176672347178850479216707 19765008520768275718825061)
      ·
        refine ⟨3705939097644051697279699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19765008520768275718825061 3705939097644051697279699)
        ·
          refine ⟨5558908646466077545919549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3705939097644051697279699 5558908646466077545919549)
          ·
            refine ⟨2084590742424779079719831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5558908646466077545919549 2084590742424779079719831)
            ·
              refine ⟨3126886113637168619579747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084590742424779079719831 3126886113637168619579747)
              ·
                refine ⟨4690329170455752929369621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3126886113637168619579747 4690329170455752929369621)
                ·
                  refine ⟨219859179865113418564201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4690329170455752929369621 219859179865113418564201)
                  ·
                    rfl

theorem cell20_481696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_481696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481696 prefixEnd_481696 := by exact prefixLift 481696
  have htrace : WordTrace (prefixWord ++ tailWord_481696) baseStart_481696 baseEnd_481696 := by
    simpa [prefixWord, tailWord_481696, baseEnd_481696] using wordTrace_append hprefix tailTrace_481696
  have hstable : (prefixWord ++ tailWord_481696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481696).length < 2 ^ (prefixWord ++ tailWord_481696).sum := by decide
  have hdescent : baseEnd_481696 < baseStart_481696 := by decide
  rcases family_descends (prefixWord ++ tailWord_481696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481716 : List Nat := [2, 5, 2, 2, 1, 1, 7]
def baseStart_481716 : Nat := 118140960795 + 481716 * 2 ^ 59
def prefixEnd_481716 : Nat := 4983230072969 + 3 ^ 40 * 481716 * 2
def baseEnd_481716 : Nat := 24429812045564693099717

theorem tailTrace_481716 : CollatzResearch.WordTrace tailWord_481716 prefixEnd_481716 24429812045564693099717 := by
  unfold tailWord_481716
  simp only [CollatzResearch.WordTrace]
  refine ⟨8784812961416338694008501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11713083948555118258678001 8784812961416338694008501)
  ·
    refine ⟨823576215132781752563297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8784812961416338694008501 823576215132781752563297)
    ·
      refine ⟨617682161349586314422473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 823576215132781752563297 617682161349586314422473)
      ·
        refine ⟨463261621012189735816855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617682161349586314422473 463261621012189735816855)
        ·
          refine ⟨694892431518284603725283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463261621012189735816855 694892431518284603725283)
          ·
            refine ⟨1042338647277426905587925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694892431518284603725283 1042338647277426905587925)
            ·
              refine ⟨24429812045564693099717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1042338647277426905587925 24429812045564693099717)
              ·
                rfl

theorem cell20_481716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 7].length) (baseStart_481716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481716 prefixEnd_481716 := by exact prefixLift 481716
  have htrace : WordTrace (prefixWord ++ tailWord_481716) baseStart_481716 baseEnd_481716 := by
    simpa [prefixWord, tailWord_481716, baseEnd_481716] using wordTrace_append hprefix tailTrace_481716
  have hstable : (prefixWord ++ tailWord_481716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481716).length < 2 ^ (prefixWord ++ tailWord_481716).sum := by decide
  have hdescent : baseEnd_481716 < baseStart_481716 := by decide
  rcases family_descends (prefixWord ++ tailWord_481716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481768 : List Nat := [2, 1, 4, 1, 1, 3, 3, 3, 2]
def baseStart_481768 : Nat := 118140960795 + 481768 * 2 ^ 59
def prefixEnd_481768 : Nat := 4983230072969 + 3 ^ 40 * 481768 * 2
def baseEnd_481768 : Nat := 219892042627001168163907

theorem tailTrace_481768 : CollatzResearch.WordTrace tailWord_481768 prefixEnd_481768 219892042627001168163907 := by
  unfold tailWord_481768
  simp only [CollatzResearch.WordTrace]
  refine ⟨8785761259322145134454979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11714348345762860179273305 8785761259322145134454979)
  ·
    refine ⟨13178641888983217701682469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8785761259322145134454979 13178641888983217701682469)
    ·
      refine ⟨2470995354184353319065463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13178641888983217701682469 2470995354184353319065463)
      ·
        refine ⟨3706493031276529978598195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2470995354184353319065463 3706493031276529978598195)
        ·
          refine ⟨5559739546914794967897293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706493031276529978598195 5559739546914794967897293)
          ·
            refine ⟨2084902330093048112961485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5559739546914794967897293 2084902330093048112961485)
            ·
              refine ⟨781838373784893042360557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2084902330093048112961485 781838373784893042360557)
              ·
                refine ⟨293189390169334890885209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 781838373784893042360557 293189390169334890885209)
                ·
                  refine ⟨219892042627001168163907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293189390169334890885209 219892042627001168163907)
                  ·
                    rfl

theorem cell20_481768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 2].length) (baseStart_481768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481768 prefixEnd_481768 := by exact prefixLift 481768
  have htrace : WordTrace (prefixWord ++ tailWord_481768) baseStart_481768 baseEnd_481768 := by
    simpa [prefixWord, tailWord_481768, baseEnd_481768] using wordTrace_append hprefix tailTrace_481768
  have hstable : (prefixWord ++ tailWord_481768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481768).length < 2 ^ (prefixWord ++ tailWord_481768).sum := by decide
  have hdescent : baseEnd_481768 < baseStart_481768 := by decide
  rcases family_descends (prefixWord ++ tailWord_481768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481782 : List Nat := [5, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_481782 : Nat := 118140960795 + 481782 * 2 ^ 59
def prefixEnd_481782 : Nat := 4983230072969 + 3 ^ 40 * 481782 * 2
def baseEnd_481782 : Nat := 219898432608479341697183

theorem tailTrace_481782 : CollatzResearch.WordTrace tailWord_481782 prefixEnd_481782 219898432608479341697183 := by
  unfold tailWord_481782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1098252071287098166244975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11714688760395713773279733 1098252071287098166244975)
  ·
    refine ⟨1647378106930647249367463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1098252071287098166244975 1647378106930647249367463)
    ·
      refine ⟨2471067160395970874051195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1647378106930647249367463 2471067160395970874051195)
      ·
        refine ⟨3706600740593956311076793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2471067160395970874051195 3706600740593956311076793)
        ·
          refine ⟨2779950555445467233307595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3706600740593956311076793 2779950555445467233307595)
          ·
            refine ⟨4169925833168200849961393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779950555445467233307595 4169925833168200849961393)
            ·
              refine ⟨3127444374876150637471045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4169925833168200849961393 3127444374876150637471045)
              ·
                refine ⟨586395820289278244525821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3127444374876150637471045 586395820289278244525821)
                ·
                  refine ⟨219898432608479341697183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586395820289278244525821 219898432608479341697183)
                  ·
                    rfl

theorem cell20_481782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_481782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481782 prefixEnd_481782 := by exact prefixLift 481782
  have htrace : WordTrace (prefixWord ++ tailWord_481782) baseStart_481782 baseEnd_481782 := by
    simpa [prefixWord, tailWord_481782, baseEnd_481782] using wordTrace_append hprefix tailTrace_481782
  have hstable : (prefixWord ++ tailWord_481782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481782).length < 2 ^ (prefixWord ++ tailWord_481782).sum := by decide
  have hdescent : baseEnd_481782 < baseStart_481782 := by decide
  rcases family_descends (prefixWord ++ tailWord_481782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481796 : List Nat := [2, 3, 2, 3, 1, 1, 1, 7]
def baseStart_481796 : Nat := 118140960795 + 481796 * 2 ^ 59
def prefixEnd_481796 : Nat := 4983230072969 + 3 ^ 40 * 481796 * 2
def baseEnd_481796 : Nat := 73301607529985838410153

theorem tailTrace_481796 : CollatzResearch.WordTrace tailWord_481796 prefixEnd_481796 73301607529985838410153 := by
  unfold tailWord_481796
  simp only [CollatzResearch.WordTrace]
  refine ⟨8786271881271425525464621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11715029175028567367286161 8786271881271425525464621)
  ·
    refine ⟨3294851955476784572049233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8786271881271425525464621 3294851955476784572049233)
    ·
      refine ⟨2471138966607588429036925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3294851955476784572049233 2471138966607588429036925)
      ·
        refine ⟨926677112477845660888847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2471138966607588429036925 926677112477845660888847)
        ·
          refine ⟨1390015668716768491333271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926677112477845660888847 1390015668716768491333271)
          ·
            refine ⟨2085023503075152736999907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390015668716768491333271 2085023503075152736999907)
            ·
              refine ⟨3127535254612729105499861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085023503075152736999907 3127535254612729105499861)
              ·
                refine ⟨73301607529985838410153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3127535254612729105499861 73301607529985838410153)
                ·
                  rfl

theorem cell20_481796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_481796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481796 prefixEnd_481796 := by exact prefixLift 481796
  have htrace : WordTrace (prefixWord ++ tailWord_481796) baseStart_481796 baseEnd_481796 := by
    simpa [prefixWord, tailWord_481796, baseEnd_481796] using wordTrace_append hprefix tailTrace_481796
  have hstable : (prefixWord ++ tailWord_481796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481796).length < 2 ^ (prefixWord ++ tailWord_481796).sum := by decide
  have hdescent : baseEnd_481796 < baseStart_481796 := by decide
  rcases family_descends (prefixWord ++ tailWord_481796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481841 : List Nat := [1, 2, 2, 3, 1, 1, 3, 4, 3]
def baseStart_481841 : Nat := 118140960795 + 481841 * 2 ^ 59
def prefixEnd_481841 : Nat := 4983230072969 + 3 ^ 40 * 481841 * 2
def baseEnd_481841 : Nat := 219925361816137358730275

theorem tailTrace_481841 : CollatzResearch.WordTrace tailWord_481841 prefixEnd_481841 219925361816137358730275 := by
  unfold tailWord_481841
  simp only [CollatzResearch.WordTrace]
  refine ⟨17574185047379823736317377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11716123364919882490878251 17574185047379823736317377)
  ·
    refine ⟨13180638785534867802238033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17574185047379823736317377 13180638785534867802238033)
    ·
      refine ⟨9885479089151150851678525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13180638785534867802238033 9885479089151150851678525)
      ·
        refine ⟨3707054658431681569379447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9885479089151150851678525 3707054658431681569379447)
        ·
          refine ⟨5560581987647522354069171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3707054658431681569379447 5560581987647522354069171)
          ·
            refine ⟨8340872981471283531103757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5560581987647522354069171 8340872981471283531103757)
            ·
              refine ⟨3127827368051731324163909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8340872981471283531103757 3127827368051731324163909)
              ·
                refine ⟨586467631509699623280733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3127827368051731324163909 586467631509699623280733)
                ·
                  refine ⟨219925361816137358730275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586467631509699623280733 219925361816137358730275)
                  ·
                    rfl

theorem cell20_481841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_481841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481841 prefixEnd_481841 := by exact prefixLift 481841
  have htrace : WordTrace (prefixWord ++ tailWord_481841) baseStart_481841 baseEnd_481841 := by
    simpa [prefixWord, tailWord_481841, baseEnd_481841] using wordTrace_append hprefix tailTrace_481841
  have hstable : (prefixWord ++ tailWord_481841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481841).length < 2 ^ (prefixWord ++ tailWord_481841).sum := by decide
  have hdescent : baseEnd_481841 < baseStart_481841 := by decide
  rcases family_descends (prefixWord ++ tailWord_481841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481848 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 4]
def baseStart_481848 : Nat := 118140960795 + 481848 * 2 ^ 59
def prefixEnd_481848 : Nat := 4983230072969 + 3 ^ 40 * 481848 * 2
def baseEnd_481848 : Nat := 219928556806876445496913

theorem tailTrace_481848 : CollatzResearch.WordTrace tailWord_481848 prefixEnd_481848 219928556806876445496913 := by
  unfold tailWord_481848
  simp only [CollatzResearch.WordTrace]
  refine ⟨8787220179177231965911099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11716293572236309287881465 8787220179177231965911099)
  ·
    refine ⟨13180830268765847948866649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8787220179177231965911099 13180830268765847948866649)
    ·
      refine ⟨9885622701574385961649987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13180830268765847948866649 9885622701574385961649987)
      ·
        refine ⟨14828434052361578942474981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9885622701574385961649987 14828434052361578942474981)
        ·
          refine ⟨2780331384817796051714059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14828434052361578942474981 2780331384817796051714059)
          ·
            refine ⟨4170497077226694077571089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2780331384817796051714059 4170497077226694077571089)
            ·
              refine ⟨3127872807920020558178317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4170497077226694077571089 3127872807920020558178317)
              ·
                refine ⟨1172952302970007709316869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3127872807920020558178317 1172952302970007709316869)
                ·
                  refine ⟨219928556806876445496913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1172952302970007709316869 219928556806876445496913)
                  ·
                    rfl

theorem cell20_481848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_481848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481848 prefixEnd_481848 := by exact prefixLift 481848
  have htrace : WordTrace (prefixWord ++ tailWord_481848) baseStart_481848 baseEnd_481848 := by
    simpa [prefixWord, tailWord_481848, baseEnd_481848] using wordTrace_append hprefix tailTrace_481848
  have hstable : (prefixWord ++ tailWord_481848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481848).length < 2 ^ (prefixWord ++ tailWord_481848).sum := by decide
  have hdescent : baseEnd_481848 < baseStart_481848 := by decide
  rcases family_descends (prefixWord ++ tailWord_481848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481896 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 5]
def baseStart_481896 : Nat := 118140960795 + 481896 * 2 ^ 59
def prefixEnd_481896 : Nat := 4983230072969 + 3 ^ 40 * 481896 * 2
def baseEnd_481896 : Nat := 219950465314801611896717

theorem tailTrace_481896 : CollatzResearch.WordTrace tailWord_481896 prefixEnd_481896 219950465314801611896717 := by
  unfold tailWord_481896
  simp only [CollatzResearch.WordTrace]
  refine ⟨8788095531090284064784771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11717460708120378753046361 8788095531090284064784771)
  ·
    refine ⟨13182143296635426097177157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8788095531090284064784771 13182143296635426097177157)
    ·
      refine ⟨2471651868119142393220717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13182143296635426097177157 2471651868119142393220717)
      ·
        refine ⟨926869450544678397457769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2471651868119142393220717 926869450544678397457769)
        ·
          refine ⟨695152087908508798093327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 926869450544678397457769 695152087908508798093327)
          ·
            refine ⟨1042728131862763197139991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695152087908508798093327 1042728131862763197139991)
            ·
              refine ⟨1564092197794144795709987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042728131862763197139991 1564092197794144795709987)
              ·
                refine ⟨2346138296691217193564981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564092197794144795709987 2346138296691217193564981)
                ·
                  refine ⟨219950465314801611896717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2346138296691217193564981 219950465314801611896717)
                  ·
                    rfl

theorem cell20_481896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_481896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481896 prefixEnd_481896 := by exact prefixLift 481896
  have htrace : WordTrace (prefixWord ++ tailWord_481896) baseStart_481896 baseEnd_481896 := by
    simpa [prefixWord, tailWord_481896, baseEnd_481896] using wordTrace_append hprefix tailTrace_481896
  have hstable : (prefixWord ++ tailWord_481896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481896).length < 2 ^ (prefixWord ++ tailWord_481896).sum := by decide
  have hdescent : baseEnd_481896 < baseStart_481896 := by decide
  rcases family_descends (prefixWord ++ tailWord_481896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481903 : List Nat := [1, 1, 2, 1, 3, 2, 4, 4, 2]
def baseStart_481903 : Nat := 118140960795 + 481903 * 2 ^ 59
def prefixEnd_481903 : Nat := 4983230072969 + 3 ^ 40 * 481903 * 2
def baseEnd_481903 : Nat := 219953660305540698663355

theorem tailTrace_481903 : CollatzResearch.WordTrace tailWord_481903 prefixEnd_481903 219953660305540698663355 := by
  unfold tailWord_481903
  simp only [CollatzResearch.WordTrace]
  refine ⟨17576446373155208325074363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11717630915436805550049575 17576446373155208325074363)
  ·
    refine ⟨26364669559732812487611545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17576446373155208325074363 26364669559732812487611545)
    ·
      refine ⟨19773502169799609365708659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26364669559732812487611545 19773502169799609365708659)
      ·
        refine ⟨29660253254699414048562989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19773502169799609365708659 29660253254699414048562989)
        ·
          refine ⟨11122594970512280268211121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29660253254699414048562989 11122594970512280268211121)
          ·
            refine ⟨8341946227884210201158341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11122594970512280268211121 8341946227884210201158341)
            ·
              refine ⟨1564114917728289412717189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8341946227884210201158341 1564114917728289412717189)
              ·
                refine ⟨293271547074054264884473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1564114917728289412717189 293271547074054264884473)
                ·
                  refine ⟨219953660305540698663355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293271547074054264884473 219953660305540698663355)
                  ·
                    rfl

theorem cell20_481903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 2].length) (baseStart_481903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481903 prefixEnd_481903 := by exact prefixLift 481903
  have htrace : WordTrace (prefixWord ++ tailWord_481903) baseStart_481903 baseEnd_481903 := by
    simpa [prefixWord, tailWord_481903, baseEnd_481903] using wordTrace_append hprefix tailTrace_481903
  have hstable : (prefixWord ++ tailWord_481903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481903).length < 2 ^ (prefixWord ++ tailWord_481903).sum := by decide
  have hdescent : baseEnd_481903 < baseStart_481903 := by decide
  rcases family_descends (prefixWord ++ tailWord_481903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481948 : List Nat := [2, 2, 3, 2, 2, 3, 6]
def baseStart_481948 : Nat := 118140960795 + 481948 * 2 ^ 59
def prefixEnd_481948 : Nat := 4983230072969 + 3 ^ 40 * 481948 * 2
def baseEnd_481948 : Nat := 24441577725746726907019

theorem tailTrace_481948 : CollatzResearch.WordTrace tailWord_481948 prefixEnd_481948 24441577725746726907019 := by
  unfold tailWord_481948
  simp only [CollatzResearch.WordTrace]
  refine ⟨8789043828996090505231249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11718725105328120673641665 8789043828996090505231249)
  ·
    refine ⟨6591782871747067878923437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8789043828996090505231249 6591782871747067878923437)
    ·
      refine ⟨2471918576905150454596289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6591782871747067878923437 2471918576905150454596289)
      ·
        refine ⟨1853938932678862840947217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2471918576905150454596289 1853938932678862840947217)
        ·
          refine ⟨1390454199509147130710413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1853938932678862840947217 1390454199509147130710413)
          ·
            refine ⟨521420324815930174016405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1390454199509147130710413 521420324815930174016405)
            ·
              refine ⟨24441577725746726907019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 521420324815930174016405 24441577725746726907019)
              ·
                rfl

theorem cell20_481948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 6].length) (baseStart_481948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481948 prefixEnd_481948 := by exact prefixLift 481948
  have htrace : WordTrace (prefixWord ++ tailWord_481948) baseStart_481948 baseEnd_481948 := by
    simpa [prefixWord, tailWord_481948, baseEnd_481948] using wordTrace_append hprefix tailTrace_481948
  have hstable : (prefixWord ++ tailWord_481948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481948).length < 2 ^ (prefixWord ++ tailWord_481948).sum := by decide
  have hdescent : baseEnd_481948 < baseStart_481948 := by decide
  rcases family_descends (prefixWord ++ tailWord_481948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482031 : List Nat := [1, 1, 2, 1, 5, 2, 2, 3, 3]
def baseStart_482031 : Nat := 118140960795 + 482031 * 2 ^ 59
def prefixEnd_482031 : Nat := 4983230072969 + 3 ^ 40 * 482031 * 2
def baseEnd_482031 : Nat := 220012082993341142396165

theorem tailTrace_482031 : CollatzResearch.WordTrace tailWord_482031 prefixEnd_482031 220012082993341142396165 := by
  unfold tailWord_482031
  simp only [CollatzResearch.WordTrace]
  refine ⟨17581114916691486185733947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11720743277794324123822631 17581114916691486185733947)
  ·
    refine ⟨26371672375037229278600921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17581114916691486185733947 26371672375037229278600921)
    ·
      refine ⟨19778754281277921958950691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26371672375037229278600921 19778754281277921958950691)
      ·
        refine ⟨29668131421916882938426037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19778754281277921958950691 29668131421916882938426037)
        ·
          refine ⟨2781387320804707775477441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29668131421916882938426037 2781387320804707775477441)
          ·
            refine ⟨2086040490603530831608081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2781387320804707775477441 2086040490603530831608081)
            ·
              refine ⟨1564530367952648123706061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2086040490603530831608081 1564530367952648123706061)
              ·
                refine ⟨586698887982243046389773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1564530367952648123706061 586698887982243046389773)
                ·
                  refine ⟨220012082993341142396165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586698887982243046389773 220012082993341142396165)
                  ·
                    rfl

theorem cell20_482031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 3].length) (baseStart_482031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482031 prefixEnd_482031 := by exact prefixLift 482031
  have htrace : WordTrace (prefixWord ++ tailWord_482031) baseStart_482031 baseEnd_482031 := by
    simpa [prefixWord, tailWord_482031, baseEnd_482031] using wordTrace_append hprefix tailTrace_482031
  have hstable : (prefixWord ++ tailWord_482031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482031).length < 2 ^ (prefixWord ++ tailWord_482031).sum := by decide
  have hdescent : baseEnd_482031 < baseStart_482031 := by decide
  rcases family_descends (prefixWord ++ tailWord_482031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482037 : List Nat := [1, 3, 6, 1, 1, 1, 3, 4]
def baseStart_482037 : Nat := 118140960795 + 482037 * 2 ^ 59
def prefixEnd_482037 : Nat := 4983230072969 + 3 ^ 40 * 482037 * 2
def baseEnd_482037 : Nat := 73338273852277262732047

theorem tailTrace_482037 : CollatzResearch.WordTrace tailWord_482037 prefixEnd_482037 73338273852277262732047 := by
  unfold tailWord_482037
  simp only [CollatzResearch.WordTrace]
  refine ⟨17581333754669749210452365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11720889169779832806968243 17581333754669749210452365)
  ·
    refine ⟨6593000158001155953919637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17581333754669749210452365 6593000158001155953919637)
    ·
      refine ⟨309046882406304185339983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6593000158001155953919637 309046882406304185339983)
      ·
        refine ⟨463570323609456278009975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309046882406304185339983 463570323609456278009975)
        ·
          refine ⟨695355485414184417014963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463570323609456278009975 695355485414184417014963)
          ·
            refine ⟨1043033228121276625522445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695355485414184417014963 1043033228121276625522445)
            ·
              refine ⟨391137460545478734570917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1043033228121276625522445 391137460545478734570917)
              ·
                refine ⟨73338273852277262732047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 391137460545478734570917 73338273852277262732047)
                ·
                  rfl

theorem cell20_482037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 4].length) (baseStart_482037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482037 prefixEnd_482037 := by exact prefixLift 482037
  have htrace : WordTrace (prefixWord ++ tailWord_482037) baseStart_482037 baseEnd_482037 := by
    simpa [prefixWord, tailWord_482037, baseEnd_482037] using wordTrace_append hprefix tailTrace_482037
  have hstable : (prefixWord ++ tailWord_482037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482037).length < 2 ^ (prefixWord ++ tailWord_482037).sum := by decide
  have hdescent : baseEnd_482037 < baseStart_482037 := by decide
  rcases family_descends (prefixWord ++ tailWord_482037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482059 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 8]
def baseStart_482059 : Nat := 118140960795 + 482059 * 2 ^ 59
def prefixEnd_482059 : Nat := 4983230072969 + 3 ^ 40 * 482059 * 2
def baseEnd_482059 : Nat := 220024862956297489462717

theorem tailTrace_482059 : CollatzResearch.WordTrace tailWord_482059 prefixEnd_482059 220024862956297489462717 := by
  unfold tailWord_482059
  simp only [CollatzResearch.WordTrace]
  refine ⟨17582136160590046967753231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11721424107060031311835487 17582136160590046967753231)
  ·
    refine ⟨26373204240885070451629847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17582136160590046967753231 26373204240885070451629847)
    ·
      refine ⟨39559806361327605677444771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26373204240885070451629847 39559806361327605677444771)
      ·
        refine ⟨59339709541991408516167157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39559806361327605677444771 59339709541991408516167157)
        ·
          refine ⟨5563097769561694548390671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59339709541991408516167157 5563097769561694548390671)
          ·
            refine ⟨8344646654342541822586007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5563097769561694548390671 8344646654342541822586007)
            ·
              refine ⟨12516969981513812733879011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8344646654342541822586007 12516969981513812733879011)
              ·
                refine ⟨18775454972270719100818517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12516969981513812733879011 18775454972270719100818517)
                ·
                  refine ⟨220024862956297489462717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18775454972270719100818517 220024862956297489462717)
                  ·
                    rfl

theorem cell20_482059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_482059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482059 prefixEnd_482059 := by exact prefixLift 482059
  have htrace : WordTrace (prefixWord ++ tailWord_482059) baseStart_482059 baseEnd_482059 := by
    simpa [prefixWord, tailWord_482059, baseEnd_482059] using wordTrace_append hprefix tailTrace_482059
  have hstable : (prefixWord ++ tailWord_482059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482059).length < 2 ^ (prefixWord ++ tailWord_482059).sum := by decide
  have hdescent : baseEnd_482059 < baseStart_482059 := by decide
  rcases family_descends (prefixWord ++ tailWord_482059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482076 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 4]
def baseStart_482076 : Nat := 118140960795 + 482076 * 2 ^ 59
def prefixEnd_482076 : Nat := 4983230072969 + 3 ^ 40 * 482076 * 2
def baseEnd_482076 : Nat := 220032622219520985895981

theorem tailTrace_482076 : CollatzResearch.WordTrace tailWord_482076 prefixEnd_482076 220032622219520985895981 := by
  unfold tailWord_482076
  simp only [CollatzResearch.WordTrace]
  refine ⟨8791378100764229435561041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11721837467685639247414721 8791378100764229435561041)
  ·
    refine ⟨6593533575573172076670781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8791378100764229435561041 6593533575573172076670781)
    ·
      refine ⟨2472575090839939528751543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6593533575573172076670781 2472575090839939528751543)
      ·
        refine ⟨3708862636259909293127315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2472575090839939528751543 3708862636259909293127315)
        ·
          refine ⟨5563293954389863939690973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3708862636259909293127315 5563293954389863939690973)
          ·
            refine ⟨2086235232896198977384115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5563293954389863939690973 2086235232896198977384115)
            ·
              refine ⟨3129352849344298466076173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086235232896198977384115 3129352849344298466076173)
              ·
                refine ⟨1173507318504111924778565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3129352849344298466076173 1173507318504111924778565)
                ·
                  refine ⟨220032622219520985895981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1173507318504111924778565 220032622219520985895981)
                  ·
                    rfl

theorem cell20_482076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_482076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482076 prefixEnd_482076 := by exact prefixLift 482076
  have htrace : WordTrace (prefixWord ++ tailWord_482076) baseStart_482076 baseEnd_482076 := by
    simpa [prefixWord, tailWord_482076, baseEnd_482076] using wordTrace_append hprefix tailTrace_482076
  have hstable : (prefixWord ++ tailWord_482076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482076).length < 2 ^ (prefixWord ++ tailWord_482076).sum := by decide
  have hdescent : baseEnd_482076 < baseStart_482076 := by decide
  rcases family_descends (prefixWord ++ tailWord_482076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482121 : List Nat := [1, 2, 1, 1, 2, 7, 6]
def baseStart_482121 : Nat := 118140960795 + 482121 * 2 ^ 59
def prefixEnd_482121 : Nat := 4983230072969 + 3 ^ 40 * 482121 * 2
def baseEnd_482121 : Nat := 24450351271744536599533

theorem tailTrace_482121 : CollatzResearch.WordTrace tailWord_482121 prefixEnd_482121 24450351271744536599533 := by
  unfold tailWord_482121
  simp only [CollatzResearch.WordTrace]
  refine ⟨17584397486365431556510217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11722931657576954371006811 17584397486365431556510217)
  ·
    refine ⟨13188298114774073667382663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17584397486365431556510217 13188298114774073667382663)
    ·
      refine ⟨19782447172161110501073995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13188298114774073667382663 19782447172161110501073995)
      ·
        refine ⟨29673670758241665751610993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19782447172161110501073995 29673670758241665751610993)
        ·
          refine ⟨22255253068681249313708245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29673670758241665751610993 22255253068681249313708245)
          ·
            refine ⟨521607493797216780790037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 22255253068681249313708245 521607493797216780790037)
            ·
              refine ⟨24450351271744536599533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 521607493797216780790037 24450351271744536599533)
              ·
                rfl

theorem cell20_482121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 6].length) (baseStart_482121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482121 prefixEnd_482121 := by exact prefixLift 482121
  have htrace : WordTrace (prefixWord ++ tailWord_482121) baseStart_482121 baseEnd_482121 := by
    simpa [prefixWord, tailWord_482121, baseEnd_482121] using wordTrace_append hprefix tailTrace_482121
  have hstable : (prefixWord ++ tailWord_482121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482121).length < 2 ^ (prefixWord ++ tailWord_482121).sum := by decide
  have hdescent : baseEnd_482121 < baseStart_482121 := by decide
  rcases family_descends (prefixWord ++ tailWord_482121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482128 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 5]
def baseStart_482128 : Nat := 118140960795 + 482128 * 2 ^ 59
def prefixEnd_482128 : Nat := 4983230072969 + 3 ^ 40 * 482128 * 2
def baseEnd_482128 : Nat := 220056356436439916162435

theorem tailTrace_482128 : CollatzResearch.WordTrace tailWord_482128 prefixEnd_482128 220056356436439916162435 := by
  unfold tailWord_482128
  simp only [CollatzResearch.WordTrace]
  refine ⟨8792326398670035876007519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11723101864893381168010025 8792326398670035876007519)
  ·
    refine ⟨13188489598005053814011279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8792326398670035876007519 13188489598005053814011279)
    ·
      refine ⟨19782734397007580721016919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13188489598005053814011279 19782734397007580721016919)
      ·
        refine ⟨29674101595511371081525379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19782734397007580721016919 29674101595511371081525379)
        ·
          refine ⟨44511152393267056622288069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29674101595511371081525379 44511152393267056622288069)
          ·
            refine ⟨8345841073737573116679013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44511152393267056622288069 8345841073737573116679013)
            ·
              refine ⟨1564845201325794959377315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8345841073737573116679013 1564845201325794959377315)
              ·
                refine ⟨2347267801988692439065973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564845201325794959377315 2347267801988692439065973)
                ·
                  refine ⟨220056356436439916162435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2347267801988692439065973 220056356436439916162435)
                  ·
                    rfl

theorem cell20_482128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_482128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482128 prefixEnd_482128 := by exact prefixLift 482128
  have htrace : WordTrace (prefixWord ++ tailWord_482128) baseStart_482128 baseEnd_482128 := by
    simpa [prefixWord, tailWord_482128, baseEnd_482128] using wordTrace_append hprefix tailTrace_482128
  have hstable : (prefixWord ++ tailWord_482128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482128).length < 2 ^ (prefixWord ++ tailWord_482128).sum := by decide
  have hdescent : baseEnd_482128 < baseStart_482128 := by decide
  rcases family_descends (prefixWord ++ tailWord_482128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482178 : List Nat := [3, 4, 2, 2, 2, 1, 2, 2, 2]
def baseStart_482178 : Nat := 118140960795 + 482178 * 2 ^ 59
def prefixEnd_482178 : Nat := 4983230072969 + 3 ^ 40 * 482178 * 2
def baseEnd_482178 : Nat := 220079177798861964495565

theorem tailTrace_482178 : CollatzResearch.WordTrace tailWord_482178 prefixEnd_482178 220079177798861964495565 := by
  unfold tailWord_482178
  simp only [CollatzResearch.WordTrace]
  refine ⟨4396619111789732572833797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11724317631439286860890125 4396619111789732572833797)
  ·
    refine ⟨824366083460574857406337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4396619111789732572833797 824366083460574857406337)
    ·
      refine ⟨618274562595431143054753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 824366083460574857406337 618274562595431143054753)
      ·
        refine ⟨463705921946573357291065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 618274562595431143054753 463705921946573357291065)
        ·
          refine ⟨347779441459930017968299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463705921946573357291065 347779441459930017968299)
          ·
            refine ⟨521669162189895026952449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347779441459930017968299 521669162189895026952449)
            ·
              refine ⟨391251871642421270214337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 521669162189895026952449 391251871642421270214337)
              ·
                refine ⟨293438903731815952660753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391251871642421270214337 293438903731815952660753)
                ·
                  refine ⟨220079177798861964495565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293438903731815952660753 220079177798861964495565)
                  ·
                    rfl

theorem cell20_482178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_482178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482178 prefixEnd_482178 := by exact prefixLift 482178
  have htrace : WordTrace (prefixWord ++ tailWord_482178) baseStart_482178 baseEnd_482178 := by
    simpa [prefixWord, tailWord_482178, baseEnd_482178] using wordTrace_append hprefix tailTrace_482178
  have hstable : (prefixWord ++ tailWord_482178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482178).length < 2 ^ (prefixWord ++ tailWord_482178).sum := by decide
  have hdescent : baseEnd_482178 < baseStart_482178 := by decide
  rcases family_descends (prefixWord ++ tailWord_482178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482183 : List Nat := [1, 1, 4, 2, 3, 1, 1, 4, 3]
def baseStart_482183 : Nat := 118140960795 + 482183 * 2 ^ 59
def prefixEnd_482183 : Nat := 4983230072969 + 3 ^ 40 * 482183 * 2
def baseEnd_482183 : Nat := 220081459935104169328877

theorem tailTrace_482183 : CollatzResearch.WordTrace tailWord_482183 prefixEnd_482183 220081459935104169328877 := by
  unfold tailWord_482183
  simp only [CollatzResearch.WordTrace]
  refine ⟨17586658812140816145267203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11724439208093877430178135 17586658812140816145267203)
  ·
    refine ⟨26379988218211224217900805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17586658812140816145267203 26379988218211224217900805)
    ·
      refine ⟨4946247790914604540856401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26379988218211224217900805 4946247790914604540856401)
      ·
        refine ⟨3709685843185953405642301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4946247790914604540856401 3709685843185953405642301)
        ·
          refine ⟨1391132191194732527115863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3709685843185953405642301 1391132191194732527115863)
          ·
            refine ⟨2086698286792098790673795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391132191194732527115863 2086698286792098790673795)
            ·
              refine ⟨3130047430188148186010693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086698286792098790673795 3130047430188148186010693)
              ·
                refine ⟨586883893160277784877005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3130047430188148186010693 586883893160277784877005)
                ·
                  refine ⟨220081459935104169328877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586883893160277784877005 220081459935104169328877)
                  ·
                    rfl

theorem cell20_482183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 3].length) (baseStart_482183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482183 prefixEnd_482183 := by exact prefixLift 482183
  have htrace : WordTrace (prefixWord ++ tailWord_482183) baseStart_482183 baseEnd_482183 := by
    simpa [prefixWord, tailWord_482183, baseEnd_482183] using wordTrace_append hprefix tailTrace_482183
  have hstable : (prefixWord ++ tailWord_482183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482183).length < 2 ^ (prefixWord ++ tailWord_482183).sum := by decide
  have hdescent : baseEnd_482183 < baseStart_482183 := by decide
  rcases family_descends (prefixWord ++ tailWord_482183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482186 : List Nat := [3, 1, 2, 4, 1, 2, 1, 4, 2]
def baseStart_482186 : Nat := 118140960795 + 482186 * 2 ^ 59
def prefixEnd_482186 : Nat := 4983230072969 + 3 ^ 40 * 482186 * 2
def baseEnd_482186 : Nat := 220082829216849492228865

theorem tailTrace_482186 : CollatzResearch.WordTrace tailWord_482186 prefixEnd_482186 220082829216849492228865 := by
  unfold tailWord_482186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4396692057782486914406603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11724512154086631771750941 4396692057782486914406603)
  ·
    refine ⟨6595038086673730371609905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4396692057782486914406603 6595038086673730371609905)
    ·
      refine ⟨4946278565005297778707429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6595038086673730371609905 4946278565005297778707429)
      ·
        refine ⟨927427230938493333507643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4946278565005297778707429 927427230938493333507643)
        ·
          refine ⟨1391140846407740000261465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927427230938493333507643 1391140846407740000261465)
          ·
            refine ⟨1043355634805805000196099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1391140846407740000261465 1043355634805805000196099)
            ·
              refine ⟨1565033452208707500294149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1043355634805805000196099 1565033452208707500294149)
              ·
                refine ⟨293443772289132656305153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1565033452208707500294149 293443772289132656305153)
                ·
                  refine ⟨220082829216849492228865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293443772289132656305153 220082829216849492228865)
                  ·
                    rfl

theorem cell20_482186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_482186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482186 prefixEnd_482186 := by exact prefixLift 482186
  have htrace : WordTrace (prefixWord ++ tailWord_482186) baseStart_482186 baseEnd_482186 := by
    simpa [prefixWord, tailWord_482186, baseEnd_482186] using wordTrace_append hprefix tailTrace_482186
  have hstable : (prefixWord ++ tailWord_482186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482186).length < 2 ^ (prefixWord ++ tailWord_482186).sum := by decide
  have hdescent : baseEnd_482186 < baseStart_482186 := by decide
  rcases family_descends (prefixWord ++ tailWord_482186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482197 : List Nat := [1, 3, 2, 1, 1, 4, 3, 5]
def baseStart_482197 : Nat := 118140960795 + 482197 * 2 ^ 59
def prefixEnd_482197 : Nat := 4983230072969 + 3 ^ 40 * 482197 * 2
def baseEnd_482197 : Nat := 73362616638860780954051

theorem tailTrace_482197 : CollatzResearch.WordTrace tailWord_482197 prefixEnd_482197 73362616638860780954051 := by
  unfold tailWord_482197
  simp only [CollatzResearch.WordTrace]
  refine ⟨17587169434090096536276845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11724779622726731024184563 17587169434090096536276845)
  ·
    refine ⟨6595188537783786201103817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17587169434090096536276845 6595188537783786201103817)
    ·
      refine ⟨4946391403337839650827863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6595188537783786201103817 4946391403337839650827863)
      ·
        refine ⟨7419587105006759476241795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4946391403337839650827863 7419587105006759476241795)
        ·
          refine ⟨11129380657510139214362693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7419587105006759476241795 11129380657510139214362693)
          ·
            refine ⟨2086758873283151102693005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11129380657510139214362693 2086758873283151102693005)
            ·
              refine ⟨782534577481181663509877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2086758873283151102693005 782534577481181663509877)
              ·
                refine ⟨73362616638860780954051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 782534577481181663509877 73362616638860780954051)
                ·
                  rfl

theorem cell20_482197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 5].length) (baseStart_482197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482197 prefixEnd_482197 := by exact prefixLift 482197
  have htrace : WordTrace (prefixWord ++ tailWord_482197) baseStart_482197 baseEnd_482197 := by
    simpa [prefixWord, tailWord_482197, baseEnd_482197] using wordTrace_append hprefix tailTrace_482197
  have hstable : (prefixWord ++ tailWord_482197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482197).length < 2 ^ (prefixWord ++ tailWord_482197).sum := by decide
  have hdescent : baseEnd_482197 < baseStart_482197 := by decide
  rcases family_descends (prefixWord ++ tailWord_482197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482211 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 6]
def baseStart_482211 : Nat := 118140960795 + 482211 * 2 ^ 59
def prefixEnd_482211 : Nat := 4983230072969 + 3 ^ 40 * 482211 * 2
def baseEnd_482211 : Nat := 220094239898060516395429

theorem tailTrace_482211 : CollatzResearch.WordTrace tailWord_482211 prefixEnd_482211 220094239898060516395429 := by
  unfold tailWord_482211
  simp only [CollatzResearch.WordTrace]
  refine ⟨17587680056039376927286487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11725120037359584618190991 17587680056039376927286487)
  ·
    refine ⟨26381520084059065390929731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17587680056039376927286487 26381520084059065390929731)
    ·
      refine ⟨39572280126088598086394597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26381520084059065390929731 39572280126088598086394597)
      ·
        refine ⟨7419802523641612141198987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39572280126088598086394597 7419802523641612141198987)
        ·
          refine ⟨11129703785462418211798481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7419802523641612141198987 11129703785462418211798481)
          ·
            refine ⟨8347277839096813658848861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11129703785462418211798481 8347277839096813658848861)
            ·
              refine ⟨3130229189661305122068323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8347277839096813658848861 3130229189661305122068323)
              ·
                refine ⟨4695343784491957683102485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3130229189661305122068323 4695343784491957683102485)
                ·
                  refine ⟨220094239898060516395429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4695343784491957683102485 220094239898060516395429)
                  ·
                    rfl

theorem cell20_482211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_482211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482211 prefixEnd_482211 := by exact prefixLift 482211
  have htrace : WordTrace (prefixWord ++ tailWord_482211) baseStart_482211 baseEnd_482211 := by
    simpa [prefixWord, tailWord_482211, baseEnd_482211] using wordTrace_append hprefix tailTrace_482211
  have hstable : (prefixWord ++ tailWord_482211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482211).length < 2 ^ (prefixWord ++ tailWord_482211).sum := by decide
  have hdescent : baseEnd_482211 < baseStart_482211 := by decide
  rcases family_descends (prefixWord ++ tailWord_482211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482230 : List Nat := [5, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_482230 : Nat := 118140960795 + 482230 * 2 ^ 59
def prefixEnd_482230 : Nat := 4983230072969 + 3 ^ 40 * 482230 * 2
def baseEnd_482230 : Nat := 220102912015780894762019

theorem tailTrace_482230 : CollatzResearch.WordTrace tailWord_482230 prefixEnd_482230 220102912015780894762019 := by
  unfold tailWord_482230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1099273315185658948264259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11725582028647028781485429 1099273315185658948264259)
  ·
    refine ⟨1648909972778488422396389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1099273315185658948264259 1648909972778488422396389)
    ·
      refine ⟨309170619895966579199323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1648909972778488422396389 309170619895966579199323)
      ·
        refine ⟨463755929843949868798985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309170619895966579199323 463755929843949868798985)
        ·
          refine ⟨347816947382962401599239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463755929843949868798985 347816947382962401599239)
          ·
            refine ⟨521725421074443602398859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347816947382962401599239 521725421074443602398859)
            ·
              refine ⟨782588131611665403598289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521725421074443602398859 782588131611665403598289)
              ·
                refine ⟨586941098708749052698717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 782588131611665403598289 586941098708749052698717)
                ·
                  refine ⟨220102912015780894762019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586941098708749052698717 220102912015780894762019)
                  ·
                    rfl

theorem cell20_482230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_482230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482230 prefixEnd_482230 := by exact prefixLift 482230
  have htrace : WordTrace (prefixWord ++ tailWord_482230) baseStart_482230 baseEnd_482230 := by
    simpa [prefixWord, tailWord_482230, baseEnd_482230] using wordTrace_append hprefix tailTrace_482230
  have hstable : (prefixWord ++ tailWord_482230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482230).length < 2 ^ (prefixWord ++ tailWord_482230).sum := by decide
  have hdescent : baseEnd_482230 < baseStart_482230 := by decide
  rcases family_descends (prefixWord ++ tailWord_482230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482256 : List Nat := [2, 1, 1, 1, 1, 2, 3, 9]
def baseStart_482256 : Nat := 118140960795 + 482256 * 2 ^ 59
def prefixEnd_482256 : Nat := 4983230072969 + 3 ^ 40 * 482256 * 2
def baseEnd_482256 : Nat := 73371593041413453298415

theorem tailTrace_482256 : CollatzResearch.WordTrace tailWord_482256 prefixEnd_482256 73371593041413453298415 := by
  unfold tailWord_482256
  simp only [CollatzResearch.WordTrace]
  refine ⟨8794660670438174806337311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11726214227250899741783081 8794660670438174806337311)
  ·
    refine ⟨13191991005657262209505967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8794660670438174806337311 13191991005657262209505967)
    ·
      refine ⟨19787986508485893314258951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13191991005657262209505967 19787986508485893314258951)
      ·
        refine ⟨29681979762728839971388427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19787986508485893314258951 29681979762728839971388427)
        ·
          refine ⟨44522969644093259957082641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29681979762728839971388427 44522969644093259957082641)
          ·
            refine ⟨33392227233069944967811981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44522969644093259957082641 33392227233069944967811981)
            ·
              refine ⟨12522085212401229362929493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33392227233069944967811981 12522085212401229362929493)
              ·
                refine ⟨73371593041413453298415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12522085212401229362929493 73371593041413453298415)
                ·
                  rfl

theorem cell20_482256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_482256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482256 prefixEnd_482256 := by exact prefixLift 482256
  have htrace : WordTrace (prefixWord ++ tailWord_482256) baseStart_482256 baseEnd_482256 := by
    simpa [prefixWord, tailWord_482256, baseEnd_482256] using wordTrace_append hprefix tailTrace_482256
  have hstable : (prefixWord ++ tailWord_482256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482256).length < 2 ^ (prefixWord ++ tailWord_482256).sum := by decide
  have hdescent : baseEnd_482256 < baseStart_482256 := by decide
  rcases family_descends (prefixWord ++ tailWord_482256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482266 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_482266 : Nat := 118140960795 + 482266 * 2 ^ 59
def prefixEnd_482266 : Nat := 4983230072969 + 3 ^ 40 * 482266 * 2
def baseEnd_482266 : Nat := 220119343396724769561871

theorem tailTrace_482266 : CollatzResearch.WordTrace tailWord_482266 prefixEnd_482266 220119343396724769561871 := by
  unfold tailWord_482266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4397421517710030330134663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11726457380560080880359101 4397421517710030330134663)
  ·
    refine ⟨6596132276565045495201995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4397421517710030330134663 6596132276565045495201995)
    ·
      refine ⟨9894198414847568242802993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6596132276565045495201995 9894198414847568242802993)
      ·
        refine ⟨7420648811135676182102245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9894198414847568242802993 7420648811135676182102245)
        ·
          refine ⟨1391371652087939284144171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7420648811135676182102245 1391371652087939284144171)
          ·
            refine ⟨2087057478131908926216257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391371652087939284144171 2087057478131908926216257)
            ·
              refine ⟨1565293108598931694662193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2087057478131908926216257 1565293108598931694662193)
              ·
                refine ⟨1173969831449198770996645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1565293108598931694662193 1173969831449198770996645)
                ·
                  refine ⟨220119343396724769561871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1173969831449198770996645 220119343396724769561871)
                  ·
                    rfl

theorem cell20_482266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_482266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482266 prefixEnd_482266 := by exact prefixLift 482266
  have htrace : WordTrace (prefixWord ++ tailWord_482266) baseStart_482266 baseEnd_482266 := by
    simpa [prefixWord, tailWord_482266, baseEnd_482266] using wordTrace_append hprefix tailTrace_482266
  have hstable : (prefixWord ++ tailWord_482266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482266).length < 2 ^ (prefixWord ++ tailWord_482266).sum := by decide
  have hdescent : baseEnd_482266 < baseStart_482266 := by decide
  rcases family_descends (prefixWord ++ tailWord_482266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482269 : List Nat := [1, 4, 3, 1, 2, 3, 2, 4]
def baseStart_482269 : Nat := 118140960795 + 482269 * 2 ^ 59
def prefixEnd_482269 : Nat := 4983230072969 + 3 ^ 40 * 482269 * 2
def baseEnd_482269 : Nat := 73373570892823364153953

theorem tailTrace_482269 : CollatzResearch.WordTrace tailWord_482269 prefixEnd_482269 73373570892823364153953 := by
  unfold tailWord_482269
  simp only [CollatzResearch.WordTrace]
  refine ⟨17589795489829252832897861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11726530326552835221931907 17589795489829252832897861)
  ·
    refine ⟨3298086654342984906168349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17589795489829252832897861 3298086654342984906168349)
    ·
      refine ⟨1236782495378619339813131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3298086654342984906168349 1236782495378619339813131)
      ·
        refine ⟨1855173743067929009719697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1236782495378619339813131 1855173743067929009719697)
        ·
          refine ⟨1391380307300946757289773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1855173743067929009719697 1391380307300946757289773)
          ·
            refine ⟨521767615237855033983665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1391380307300946757289773 521767615237855033983665)
            ·
              refine ⟨391325711428391275487749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 521767615237855033983665 391325711428391275487749)
              ·
                refine ⟨73373570892823364153953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 391325711428391275487749 73373570892823364153953)
                ·
                  rfl

theorem cell20_482269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 4].length) (baseStart_482269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482269 prefixEnd_482269 := by exact prefixLift 482269
  have htrace : WordTrace (prefixWord ++ tailWord_482269) baseStart_482269 baseEnd_482269 := by
    simpa [prefixWord, tailWord_482269, baseEnd_482269] using wordTrace_append hprefix tailTrace_482269
  have hstable : (prefixWord ++ tailWord_482269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482269).length < 2 ^ (prefixWord ++ tailWord_482269).sum := by decide
  have hdescent : baseEnd_482269 < baseStart_482269 := by decide
  rcases family_descends (prefixWord ++ tailWord_482269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482280 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 5]
def baseStart_482280 : Nat := 118140960795 + 482280 * 2 ^ 59
def prefixEnd_482280 : Nat := 4983230072969 + 3 ^ 40 * 482280 * 2
def baseEnd_482280 : Nat := 220125733378202943095147

theorem tailTrace_482280 : CollatzResearch.WordTrace tailWord_482280 prefixEnd_482280 220125733378202943095147 := by
  unfold tailWord_482280
  simp only [CollatzResearch.WordTrace]
  refine ⟨8795098346394700855774147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11726797795192934474365529 8795098346394700855774147)
  ·
    refine ⟨13192647519592051283661221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8795098346394700855774147 13192647519592051283661221)
    ·
      refine ⟨2473621409923509615686479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13192647519592051283661221 2473621409923509615686479)
      ·
        refine ⟨3710432114885264423529719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2473621409923509615686479 3710432114885264423529719)
        ·
          refine ⟨5565648172327896635294579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3710432114885264423529719 5565648172327896635294579)
          ·
            refine ⟨8348472258491844952941869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5565648172327896635294579 8348472258491844952941869)
            ·
              refine ⟨3130677096934441857353201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8348472258491844952941869 3130677096934441857353201)
              ·
                refine ⟨2348007822700831393014901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3130677096934441857353201 2348007822700831393014901)
                ·
                  refine ⟨220125733378202943095147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2348007822700831393014901 220125733378202943095147)
                  ·
                    rfl

theorem cell20_482280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_482280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482280 prefixEnd_482280 := by exact prefixLift 482280
  have htrace : WordTrace (prefixWord ++ tailWord_482280) baseStart_482280 baseEnd_482280 := by
    simpa [prefixWord, tailWord_482280, baseEnd_482280] using wordTrace_append hprefix tailTrace_482280
  have hstable : (prefixWord ++ tailWord_482280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482280).length < 2 ^ (prefixWord ++ tailWord_482280).sum := by decide
  have hdescent : baseEnd_482280 < baseStart_482280 := by decide
  rcases family_descends (prefixWord ++ tailWord_482280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482292 : List Nat := [2, 6, 2, 1, 1, 1, 3, 2, 2]
def baseStart_482292 : Nat := 118140960795 + 482292 * 2 ^ 59
def prefixEnd_482292 : Nat := 4983230072969 + 3 ^ 40 * 482292 * 2
def baseEnd_482292 : Nat := 220131210505184234695099

theorem tailTrace_482292 : CollatzResearch.WordTrace tailWord_482292 prefixEnd_482292 220131210505184234695099 := by
  unfold tailWord_482292
  simp only [CollatzResearch.WordTrace]
  refine ⟨8795317184372963880492565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11727089579163951840656753 8795317184372963880492565)
  ·
    refine ⟨412280493017482681898089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8795317184372963880492565 412280493017482681898089)
    ·
      refine ⟨309210369763112011423567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412280493017482681898089 309210369763112011423567)
      ·
        refine ⟨463815554644668017135351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309210369763112011423567 463815554644668017135351)
        ·
          refine ⟨695723331967002025703027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463815554644668017135351 695723331967002025703027)
          ·
            refine ⟨1043584997950503038554541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695723331967002025703027 1043584997950503038554541)
            ·
              refine ⟨391344374231438639457953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1043584997950503038554541 391344374231438639457953)
              ·
                refine ⟨293508280673578979593465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391344374231438639457953 293508280673578979593465)
                ·
                  refine ⟨220131210505184234695099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293508280673578979593465 220131210505184234695099)
                  ·
                    rfl

theorem cell20_482292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_482292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482292 prefixEnd_482292 := by exact prefixLift 482292
  have htrace : WordTrace (prefixWord ++ tailWord_482292) baseStart_482292 baseEnd_482292 := by
    simpa [prefixWord, tailWord_482292, baseEnd_482292] using wordTrace_append hprefix tailTrace_482292
  have hstable : (prefixWord ++ tailWord_482292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482292).length < 2 ^ (prefixWord ++ tailWord_482292).sum := by decide
  have hdescent : baseEnd_482292 < baseStart_482292 := by decide
  rcases family_descends (prefixWord ++ tailWord_482292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482300 : List Nat := [2, 2, 2, 1, 2, 4, 3, 2, 2]
def baseStart_482300 : Nat := 118140960795 + 482300 * 2 ^ 59
def prefixEnd_482300 : Nat := 4983230072969 + 3 ^ 40 * 482300 * 2
def baseEnd_482300 : Nat := 220134861923171762428399

theorem tailTrace_482300 : CollatzResearch.WordTrace tailWord_482300 prefixEnd_482300 220134861923171762428399 := by
  unfold tailWord_482300
  simp only [CollatzResearch.WordTrace]
  refine ⟨8795463076358472563638177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11727284101811296751517569 8795463076358472563638177)
  ·
    refine ⟨6596597307268854422728633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8795463076358472563638177 6596597307268854422728633)
    ·
      refine ⟨4947447980451640817046475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6596597307268854422728633 4947447980451640817046475)
      ·
        refine ⟨7421171970677461225569713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4947447980451640817046475 7421171970677461225569713)
        ·
          refine ⟨5565878978008095919177285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7421171970677461225569713 5565878978008095919177285)
          ·
            refine ⟨1043602308376517984845741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5565878978008095919177285 1043602308376517984845741)
            ·
              refine ⟨391350865641194244317153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1043602308376517984845741 391350865641194244317153)
              ·
                refine ⟨293513149230895683237865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391350865641194244317153 293513149230895683237865)
                ·
                  refine ⟨220134861923171762428399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293513149230895683237865 220134861923171762428399)
                  ·
                    rfl

theorem cell20_482300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_482300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482300 prefixEnd_482300 := by exact prefixLift 482300
  have htrace : WordTrace (prefixWord ++ tailWord_482300) baseStart_482300 baseEnd_482300 := by
    simpa [prefixWord, tailWord_482300, baseEnd_482300] using wordTrace_append hprefix tailTrace_482300
  have hstable : (prefixWord ++ tailWord_482300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482300).length < 2 ^ (prefixWord ++ tailWord_482300).sum := by decide
  have hdescent : baseEnd_482300 < baseStart_482300 := by decide
  rcases family_descends (prefixWord ++ tailWord_482300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482311 : List Nat := [1, 1, 4, 3, 1, 1, 4, 5]
def baseStart_482311 : Nat := 118140960795 + 482311 * 2 ^ 59
def prefixEnd_482311 : Nat := 4983230072969 + 3 ^ 40 * 482311 * 2
def baseEnd_482311 : Nat := 73379960874301537687229

theorem tailTrace_482311 : CollatzResearch.WordTrace tailWord_482311 prefixEnd_482311 73379960874301537687229 := by
  unfold tailWord_482311
  simp only [CollatzResearch.WordTrace]
  refine ⟨17591327355677094005926787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11727551570451396003951191 17591327355677094005926787)
  ·
    refine ⟨26386991033515641008890181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17591327355677094005926787 26386991033515641008890181)
    ·
      refine ⟨4947560818784182689166909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26386991033515641008890181 4947560818784182689166909)
      ·
        refine ⟨1855335307044068508437591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4947560818784182689166909 1855335307044068508437591)
        ·
          refine ⟨2783002960566102762656387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1855335307044068508437591 2783002960566102762656387)
          ·
            refine ⟨4174504440849154143984581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2783002960566102762656387 4174504440849154143984581)
            ·
              refine ⟨782719582659216401997109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4174504440849154143984581 782719582659216401997109)
              ·
                refine ⟨73379960874301537687229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 782719582659216401997109 73379960874301537687229)
                ·
                  rfl

theorem cell20_482311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 5].length) (baseStart_482311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482311 prefixEnd_482311 := by exact prefixLift 482311
  have htrace : WordTrace (prefixWord ++ tailWord_482311) baseStart_482311 baseEnd_482311 := by
    simpa [prefixWord, tailWord_482311, baseEnd_482311] using wordTrace_append hprefix tailTrace_482311
  have hstable : (prefixWord ++ tailWord_482311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482311).length < 2 ^ (prefixWord ++ tailWord_482311).sum := by decide
  have hdescent : baseEnd_482311 < baseStart_482311 := by decide
  rcases family_descends (prefixWord ++ tailWord_482311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482314 : List Nat := [3, 1, 2, 2, 3, 1, 4, 1, 3]
def baseStart_482314 : Nat := 118140960795 + 482314 * 2 ^ 59
def prefixEnd_482314 : Nat := 4983230072969 + 3 ^ 40 * 482314 * 2
def baseEnd_482314 : Nat := 220141251904649935961675

theorem tailTrace_482314 : CollatzResearch.WordTrace tailWord_482314 prefixEnd_482314 220141251904649935961675 := by
  unfold tailWord_482314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4397859193666556379571499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11727624516444150345523997 4397859193666556379571499)
  ·
    refine ⟨6596788790499834569357249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4397859193666556379571499 6596788790499834569357249)
    ·
      refine ⟨4947591592874875927017937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6596788790499834569357249 4947591592874875927017937)
      ·
        refine ⟨3710693694656156945263453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4947591592874875927017937 3710693694656156945263453)
        ·
          refine ⟨1391510135496058854473795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3710693694656156945263453 1391510135496058854473795)
          ·
            refine ⟨2087265203244088281710693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391510135496058854473795 2087265203244088281710693)
            ·
              refine ⟨391362225608266552820755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2087265203244088281710693 391362225608266552820755)
              ·
                refine ⟨587043338412399829231133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391362225608266552820755 587043338412399829231133)
                ·
                  refine ⟨220141251904649935961675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 587043338412399829231133 220141251904649935961675)
                  ·
                    rfl

theorem cell20_482314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_482314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482314 prefixEnd_482314 := by exact prefixLift 482314
  have htrace : WordTrace (prefixWord ++ tailWord_482314) baseStart_482314 baseEnd_482314 := by
    simpa [prefixWord, tailWord_482314, baseEnd_482314] using wordTrace_append hprefix tailTrace_482314
  have hstable : (prefixWord ++ tailWord_482314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482314).length < 2 ^ (prefixWord ++ tailWord_482314).sum := by decide
  have hdescent : baseEnd_482314 < baseStart_482314 := by decide
  rcases family_descends (prefixWord ++ tailWord_482314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482366 : List Nat := [4, 2, 1, 3, 1, 1, 3, 5]
def baseStart_482366 : Nat := 118140960795 + 482366 * 2 ^ 59
def prefixEnd_482366 : Nat := 4983230072969 + 3 ^ 40 * 482366 * 2
def baseEnd_482366 : Nat := 73388328707189622076043

theorem tailTrace_482366 : CollatzResearch.WordTrace tailWord_482366 prefixEnd_482366 73388328707189622076043 := by
  unfold tailWord_482366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2199166671309729799897369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11728888913651892266119301 2199166671309729799897369)
  ·
    refine ⟨1649375003482297349923027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2199166671309729799897369 1649375003482297349923027)
    ·
      refine ⟨2474062505223446024884541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1649375003482297349923027 2474062505223446024884541)
      ·
        refine ⟨927773439458792259331703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2474062505223446024884541 927773439458792259331703)
        ·
          refine ⟨1391660159188188388997555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927773439458792259331703 1391660159188188388997555)
          ·
            refine ⟨2087490238782282583496333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391660159188188388997555 2087490238782282583496333)
            ·
              refine ⟨782808839543355968811125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2087490238782282583496333 782808839543355968811125)
              ·
                refine ⟨73388328707189622076043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 782808839543355968811125 73388328707189622076043)
                ·
                  rfl

theorem cell20_482366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_482366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482366 prefixEnd_482366 := by exact prefixLift 482366
  have htrace : WordTrace (prefixWord ++ tailWord_482366) baseStart_482366 baseEnd_482366 := by
    simpa [prefixWord, tailWord_482366, baseEnd_482366] using wordTrace_append hprefix tailTrace_482366
  have hstable : (prefixWord ++ tailWord_482366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482366).length < 2 ^ (prefixWord ++ tailWord_482366).sum := by decide
  have hdescent : baseEnd_482366 < baseStart_482366 := by decide
  rcases family_descends (prefixWord ++ tailWord_482366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482418 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_482418 : Nat := 118140960795 + 482418 * 2 ^ 59
def prefixEnd_482418 : Nat := 4983230072969 + 3 ^ 40 * 482418 * 2
def baseEnd_482418 : Nat := 220188720338487796494583

theorem tailTrace_482418 : CollatzResearch.WordTrace tailWord_482418 prefixEnd_482418 220188720338487796494583 := by
  unfold tailWord_482418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4398807491572362820017977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11730153310859634186714605 4398807491572362820017977)
  ·
    refine ⟨3299105618679272115013483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4398807491572362820017977 3299105618679272115013483)
    ·
      refine ⟨4948658428018908172520225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3299105618679272115013483 4948658428018908172520225)
      ·
        refine ⟨3711493821014181129390169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4948658428018908172520225 3711493821014181129390169)
        ·
          refine ⟨2783620365760635847042627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3711493821014181129390169 2783620365760635847042627)
          ·
            refine ⟨4175430548640953770563941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2783620365760635847042627 4175430548640953770563941)
            ·
              refine ⟨782893227870178831980739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4175430548640953770563941 782893227870178831980739)
              ·
                refine ⟨1174339841805268247971109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782893227870178831980739 1174339841805268247971109)
                ·
                  refine ⟨220188720338487796494583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1174339841805268247971109 220188720338487796494583)
                  ·
                    rfl

theorem cell20_482418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_482418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482418 prefixEnd_482418 := by exact prefixLift 482418
  have htrace : WordTrace (prefixWord ++ tailWord_482418) baseStart_482418 baseEnd_482418 := by
    simpa [prefixWord, tailWord_482418, baseEnd_482418] using wordTrace_append hprefix tailTrace_482418
  have hstable : (prefixWord ++ tailWord_482418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482418).length < 2 ^ (prefixWord ++ tailWord_482418).sum := by decide
  have hdescent : baseEnd_482418 < baseStart_482418 := by decide
  rcases family_descends (prefixWord ++ tailWord_482418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482432 : List Nat := [2, 1, 1, 2, 1, 3, 2, 5, 3]
def baseStart_482432 : Nat := 118140960795 + 482432 * 2 ^ 59
def prefixEnd_482432 : Nat := 4983230072969 + 3 ^ 40 * 482432 * 2
def baseEnd_482432 : Nat := 220195110319965970027859

theorem tailTrace_482432 : CollatzResearch.WordTrace tailWord_482432 prefixEnd_482432 220195110319965970027859 := by
  unfold tailWord_482432
  simp only [CollatzResearch.WordTrace]
  refine ⟨8797870294119365835540775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11730493725492487780721033 8797870294119365835540775)
  ·
    refine ⟨13196805441179048753311163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8797870294119365835540775 13196805441179048753311163)
    ·
      refine ⟨19795208161768573129966745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13196805441179048753311163 19795208161768573129966745)
      ·
        refine ⟨14846406121326429847475059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19795208161768573129966745 14846406121326429847475059)
        ·
          refine ⟨22269609181989644771212589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14846406121326429847475059 22269609181989644771212589)
          ·
            refine ⟨8351103443246116789204721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22269609181989644771212589 8351103443246116789204721)
            ·
              refine ⟨6263327582434587591903541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8351103443246116789204721 6263327582434587591903541)
              ·
                refine ⟨587186960853242586740957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6263327582434587591903541 587186960853242586740957)
                ·
                  refine ⟨220195110319965970027859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 587186960853242586740957 220195110319965970027859)
                  ·
                    rfl

theorem cell20_482432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_482432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482432 prefixEnd_482432 := by exact prefixLift 482432
  have htrace : WordTrace (prefixWord ++ tailWord_482432) baseStart_482432 baseEnd_482432 := by
    simpa [prefixWord, tailWord_482432, baseEnd_482432] using wordTrace_append hprefix tailTrace_482432
  have hstable : (prefixWord ++ tailWord_482432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482432).length < 2 ^ (prefixWord ++ tailWord_482432).sum := by decide
  have hdescent : baseEnd_482432 < baseStart_482432 := by decide
  rcases family_descends (prefixWord ++ tailWord_482432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482491 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 7]
def baseStart_482491 : Nat := 118140960795 + 482491 * 2 ^ 59
def prefixEnd_482491 : Nat := 4983230072969 + 3 ^ 40 * 482491 * 2
def baseEnd_482491 : Nat := 220222039527623987060951

theorem tailTrace_482491 : CollatzResearch.WordTrace tailWord_482491 prefixEnd_482491 220222039527623987060951 := by
  unfold tailWord_482491
  simp only [CollatzResearch.WordTrace]
  refine ⟨17597892495024984747479327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11731928330016656498319551 17597892495024984747479327)
  ·
    refine ⟨26396838742537477121218991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17597892495024984747479327 26396838742537477121218991)
    ·
      refine ⟨39595258113806215681828487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26396838742537477121218991 39595258113806215681828487)
      ·
        refine ⟨59392887170709323522742731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39595258113806215681828487 59392887170709323522742731)
        ·
          refine ⟨89089330756063985284114097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59392887170709323522742731 89089330756063985284114097)
          ·
            refine ⟨66816998067047988963085573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89089330756063985284114097 66816998067047988963085573)
            ·
              refine ⟨12528187137571497930578545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66816998067047988963085573 12528187137571497930578545)
              ·
                refine ⟨9396140353178623447933909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12528187137571497930578545 9396140353178623447933909)
                ·
                  refine ⟨220222039527623987060951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9396140353178623447933909 220222039527623987060951)
                  ·
                    rfl

theorem cell20_482491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_482491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482491 prefixEnd_482491 := by exact prefixLift 482491
  have htrace : WordTrace (prefixWord ++ tailWord_482491) baseStart_482491 baseEnd_482491 := by
    simpa [prefixWord, tailWord_482491, baseEnd_482491] using wordTrace_append hprefix tailTrace_482491
  have hstable : (prefixWord ++ tailWord_482491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482491).length < 2 ^ (prefixWord ++ tailWord_482491).sum := by decide
  have hdescent : baseEnd_482491 < baseStart_482491 := by decide
  rcases family_descends (prefixWord ++ tailWord_482491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482518 : List Nat := [5, 2, 1, 2, 2, 8]
def baseStart_482518 : Nat := 118140960795 + 482518 * 2 ^ 59
def prefixEnd_482518 : Nat := 4983230072969 + 3 ^ 40 * 482518 * 2
def baseEnd_482518 : Nat := 8156828261604884931883

theorem tailTrace_482518 : CollatzResearch.WordTrace tailWord_482518 prefixEnd_482518 8156828261604884931883 := by
  unfold tailWord_482518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1099929829120448022419513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11732584843951445572474805 1099929829120448022419513)
  ·
    refine ⟨824947371840336016814635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1099929829120448022419513 824947371840336016814635)
    ·
      refine ⟨1237421057760504025221953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 824947371840336016814635 1237421057760504025221953)
      ·
        refine ⟨928065793320378018916465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1237421057760504025221953 928065793320378018916465)
        ·
          refine ⟨696049344990283514187349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 928065793320378018916465 696049344990283514187349)
          ·
            refine ⟨8156828261604884931883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 696049344990283514187349 8156828261604884931883)
            ·
              rfl

theorem cell20_482518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 8].length) (baseStart_482518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482518 prefixEnd_482518 := by exact prefixLift 482518
  have htrace : WordTrace (prefixWord ++ tailWord_482518) baseStart_482518 baseEnd_482518 := by
    simpa [prefixWord, tailWord_482518, baseEnd_482518] using wordTrace_append hprefix tailTrace_482518
  have hstable : (prefixWord ++ tailWord_482518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482518).length < 2 ^ (prefixWord ++ tailWord_482518).sum := by decide
  have hdescent : baseEnd_482518 < baseStart_482518 := by decide
  rcases family_descends (prefixWord ++ tailWord_482518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482528 : List Nat := [2, 1, 1, 3, 1, 6, 2, 2, 2]
def baseStart_482528 : Nat := 118140960795 + 482528 * 2 ^ 59
def prefixEnd_482528 : Nat := 4983230072969 + 3 ^ 40 * 482528 * 2
def baseEnd_482528 : Nat := 220238927335816302827467

theorem tailTrace_482528 : CollatzResearch.WordTrace tailWord_482528 prefixEnd_482528 220238927335816302827467 := by
  unfold tailWord_482528
  simp only [CollatzResearch.WordTrace]
  refine ⟨8799620997945470033288119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11732827997260626711050825 8799620997945470033288119)
  ·
    refine ⟨13199431496918205049932179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8799620997945470033288119 13199431496918205049932179)
    ·
      refine ⟨19799147245377307574898269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13199431496918205049932179 19799147245377307574898269)
      ·
        refine ⟨7424680217016490340586851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19799147245377307574898269 7424680217016490340586851)
        ·
          refine ⟨11137020325524735510880277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7424680217016490340586851 11137020325524735510880277)
          ·
            refine ⟨522047827758971977072513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11137020325524735510880277 522047827758971977072513)
            ·
              refine ⟨391535870819228982804385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522047827758971977072513 391535870819228982804385)
              ·
                refine ⟨293651903114421737103289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391535870819228982804385 293651903114421737103289)
                ·
                  refine ⟨220238927335816302827467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293651903114421737103289 220238927335816302827467)
                  ·
                    rfl

theorem cell20_482528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 2].length) (baseStart_482528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482528 prefixEnd_482528 := by exact prefixLift 482528
  have htrace : WordTrace (prefixWord ++ tailWord_482528) baseStart_482528 baseEnd_482528 := by
    simpa [prefixWord, tailWord_482528, baseEnd_482528] using wordTrace_append hprefix tailTrace_482528
  have hstable : (prefixWord ++ tailWord_482528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482528).length < 2 ^ (prefixWord ++ tailWord_482528).sum := by decide
  have hdescent : baseEnd_482528 < baseStart_482528 := by decide
  rcases family_descends (prefixWord ++ tailWord_482528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482535 : List Nat := [1, 1, 5, 3, 3, 1, 1, 5]
def baseStart_482535 : Nat := 118140960795 + 482535 * 2 ^ 59
def prefixEnd_482535 : Nat := 4983230072969 + 3 ^ 40 * 482535 * 2
def baseEnd_482535 : Nat := 73414040775518463198035

theorem tailTrace_482535 : CollatzResearch.WordTrace tailWord_482535 prefixEnd_482535 73414040775518463198035 := by
  unfold tailWord_482535
  simp only [CollatzResearch.WordTrace]
  refine ⟨17599497306865580262081059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11732998204577053508054039 17599497306865580262081059)
  ·
    refine ⟨26399245960298370393121589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17599497306865580262081059 26399245960298370393121589)
    ·
      refine ⟨2474929308777972224355149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26399245960298370393121589 2474929308777972224355149)
      ·
        refine ⟨928098490791739584133181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2474929308777972224355149 928098490791739584133181)
        ·
          refine ⟨348036934046902344049943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 928098490791739584133181 348036934046902344049943)
          ·
            refine ⟨522055401070353516074915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348036934046902344049943 522055401070353516074915)
            ·
              refine ⟨783083101605530274112373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522055401070353516074915 783083101605530274112373)
              ·
                refine ⟨73414040775518463198035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 783083101605530274112373 73414040775518463198035)
                ·
                  rfl

theorem cell20_482535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 5].length) (baseStart_482535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482535 prefixEnd_482535 := by exact prefixLift 482535
  have htrace : WordTrace (prefixWord ++ tailWord_482535) baseStart_482535 baseEnd_482535 := by
    simpa [prefixWord, tailWord_482535, baseEnd_482535] using wordTrace_append hprefix tailTrace_482535
  have hstable : (prefixWord ++ tailWord_482535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482535).length < 2 ^ (prefixWord ++ tailWord_482535).sum := by decide
  have hdescent : baseEnd_482535 < baseStart_482535 := by decide
  rcases family_descends (prefixWord ++ tailWord_482535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482539 : List Nat := [1, 1, 1, 1, 2, 8, 1, 5]
def baseStart_482539 : Nat := 118140960795 + 482539 * 2 ^ 59
def prefixEnd_482539 : Nat := 4983230072969 + 3 ^ 40 * 482539 * 2
def baseEnd_482539 : Nat := 73414649345183051153585

theorem tailTrace_482539 : CollatzResearch.WordTrace tailWord_482539 prefixEnd_482539 73414649345183051153585 := by
  unfold tailWord_482539
  simp only [CollatzResearch.WordTrace]
  refine ⟨17599643198851088945226671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11733095465900725963484447 17599643198851088945226671)
  ·
    refine ⟨26399464798276633417840007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17599643198851088945226671 26399464798276633417840007)
    ·
      refine ⟨39599197197414950126760011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26399464798276633417840007 39599197197414950126760011)
      ·
        refine ⟨59398795796122425190140017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39599197197414950126760011 59398795796122425190140017)
        ·
          refine ⟨44549096847091818892605013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59398795796122425190140017 44549096847091818892605013)
          ·
            refine ⟨522059728676857252647715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 44549096847091818892605013 522059728676857252647715)
            ·
              refine ⟨783089593015285878971573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522059728676857252647715 783089593015285878971573)
              ·
                refine ⟨73414649345183051153585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 783089593015285878971573 73414649345183051153585)
                ·
                  rfl

theorem cell20_482539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 5].length) (baseStart_482539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482539 prefixEnd_482539 := by exact prefixLift 482539
  have htrace : WordTrace (prefixWord ++ tailWord_482539) baseStart_482539 baseEnd_482539 := by
    simpa [prefixWord, tailWord_482539, baseEnd_482539] using wordTrace_append hprefix tailTrace_482539
  have hstable : (prefixWord ++ tailWord_482539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482539).length < 2 ^ (prefixWord ++ tailWord_482539).sum := by decide
  have hdescent : baseEnd_482539 < baseStart_482539 := by decide
  rcases family_descends (prefixWord ++ tailWord_482539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482553 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 4]
def baseStart_482553 : Nat := 118140960795 + 482553 * 2 ^ 59
def prefixEnd_482553 : Nat := 4983230072969 + 3 ^ 40 * 482553 * 2
def baseEnd_482553 : Nat := 220250338017027326994031

theorem tailTrace_482553 : CollatzResearch.WordTrace tailWord_482553 prefixEnd_482553 220250338017027326994031 := by
  unfold tailWord_482553
  simp only [CollatzResearch.WordTrace]
  refine ⟨17600153820800369336236313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11733435880533579557490875 17600153820800369336236313)
  ·
    refine ⟨13200115365600277002177235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17600153820800369336236313 13200115365600277002177235)
    ·
      refine ⟨19800173048400415503265853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13200115365600277002177235 19800173048400415503265853)
      ·
        refine ⟨7425064893150155813724695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19800173048400415503265853 7425064893150155813724695)
        ·
          refine ⟨11137597339725233720587043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7425064893150155813724695 11137597339725233720587043)
          ·
            refine ⟨16706396009587850580880565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11137597339725233720587043 16706396009587850580880565)
            ·
              refine ⟨1566224625898860991957553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16706396009587850580880565 1566224625898860991957553)
              ·
                refine ⟨1174668469424145743968165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1566224625898860991957553 1174668469424145743968165)
                ·
                  refine ⟨220250338017027326994031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1174668469424145743968165 220250338017027326994031)
                  ·
                    rfl

theorem cell20_482553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_482553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482553 prefixEnd_482553 := by exact prefixLift 482553
  have htrace : WordTrace (prefixWord ++ tailWord_482553) baseStart_482553 baseEnd_482553 := by
    simpa [prefixWord, tailWord_482553, baseEnd_482553] using wordTrace_append hprefix tailTrace_482553
  have hstable : (prefixWord ++ tailWord_482553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482553).length < 2 ^ (prefixWord ++ tailWord_482553).sum := by decide
  have hdescent : baseEnd_482553 < baseStart_482553 := by decide
  rcases family_descends (prefixWord ++ tailWord_482553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482556 : List Nat := [2, 2, 2, 1, 5, 1, 3, 4]
def baseStart_482556 : Nat := 118140960795 + 482556 * 2 ^ 59
def prefixEnd_482556 : Nat := 4983230072969 + 3 ^ 40 * 482556 * 2
def baseEnd_482556 : Nat := 73417235766257549964673

theorem tailTrace_482556 : CollatzResearch.WordTrace tailWord_482556 prefixEnd_482556 73417235766257549964673 := by
  unfold tailWord_482556
  simp only [CollatzResearch.WordTrace]
  refine ⟨8800131619894750424297761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11733508826526333899063681 8800131619894750424297761)
  ·
    refine ⟨6600098714921062818223321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8800131619894750424297761 6600098714921062818223321)
    ·
      refine ⟨4950074036190797113667491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6600098714921062818223321 4950074036190797113667491)
      ·
        refine ⟨7425111054286195670501237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4950074036190797113667491 7425111054286195670501237)
        ·
          refine ⟨696104161339330844109491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7425111054286195670501237 696104161339330844109491)
          ·
            refine ⟨1044156242008996266164237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696104161339330844109491 1044156242008996266164237)
            ·
              refine ⟨391558590753373599811589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1044156242008996266164237 391558590753373599811589)
              ·
                refine ⟨73417235766257549964673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 391558590753373599811589 73417235766257549964673)
                ·
                  rfl

theorem cell20_482556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_482556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482556 prefixEnd_482556 := by exact prefixLift 482556
  have htrace : WordTrace (prefixWord ++ tailWord_482556) baseStart_482556 baseEnd_482556 := by
    simpa [prefixWord, tailWord_482556, baseEnd_482556] using wordTrace_append hprefix tailTrace_482556
  have hstable : (prefixWord ++ tailWord_482556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482556).length < 2 ^ (prefixWord ++ tailWord_482556).sum := by decide
  have hdescent : baseEnd_482556 < baseStart_482556 := by decide
  rcases family_descends (prefixWord ++ tailWord_482556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482584 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 5]
def baseStart_482584 : Nat := 118140960795 + 482584 * 2 ^ 59
def prefixEnd_482584 : Nat := 4983230072969 + 3 ^ 40 * 482584 * 2
def baseEnd_482584 : Nat := 220264487261728996960571

theorem tailTrace_482584 : CollatzResearch.WordTrace tailWord_482584 prefixEnd_482584 220264487261728996960571 := by
  unfold tailWord_482584
  simp only [CollatzResearch.WordTrace]
  refine ⟨8800642241844030815307403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11734189655792041087076537 8800642241844030815307403)
  ·
    refine ⟨13200963362766046222961105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8800642241844030815307403 13200963362766046222961105)
    ·
      refine ⟨9900722522074534667220829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13200963362766046222961105 9900722522074534667220829)
      ·
        refine ⟨3712770945777950500207811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9900722522074534667220829 3712770945777950500207811)
        ·
          refine ⟨5569156418666925750311717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3712770945777950500207811 5569156418666925750311717)
          ·
            refine ⟨1044216828500048578183447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5569156418666925750311717 1044216828500048578183447)
            ·
              refine ⟨1566325242750072867275171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044216828500048578183447 1566325242750072867275171)
              ·
                refine ⟨2349487864125109300912757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1566325242750072867275171 2349487864125109300912757)
                ·
                  refine ⟨220264487261728996960571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2349487864125109300912757 220264487261728996960571)
                  ·
                    rfl

theorem cell20_482584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_482584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482584 prefixEnd_482584 := by exact prefixLift 482584
  have htrace : WordTrace (prefixWord ++ tailWord_482584) baseStart_482584 baseEnd_482584 := by
    simpa [prefixWord, tailWord_482584, baseEnd_482584] using wordTrace_append hprefix tailTrace_482584
  have hstable : (prefixWord ++ tailWord_482584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482584).length < 2 ^ (prefixWord ++ tailWord_482584).sum := by decide
  have hdescent : baseEnd_482584 < baseStart_482584 := by decide
  rcases family_descends (prefixWord ++ tailWord_482584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482621 : List Nat := [1, 4, 1, 5, 1, 2, 1, 3, 2]
def baseStart_482621 : Nat := 118140960795 + 482621 * 2 ^ 59
def prefixEnd_482621 : Nat := 4983230072969 + 3 ^ 40 * 482621 * 2
def baseEnd_482621 : Nat := 220281375069921312727087

theorem tailTrace_482621 : CollatzResearch.WordTrace tailWord_482621 prefixEnd_482621 220281375069921312727087 := by
  unfold tailWord_482621
  simp only [CollatzResearch.WordTrace]
  refine ⟨17602633984554016949711717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11735089323036011299807811 17602633984554016949711717)
  ·
    refine ⟨3300493872103878178070947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17602633984554016949711717 3300493872103878178070947)
    ·
      refine ⟨4950740808155817267106421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3300493872103878178070947 4950740808155817267106421)
      ·
        refine ⟨464131950764607868791227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4950740808155817267106421 464131950764607868791227)
        ·
          refine ⟨696197926146911803186841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464131950764607868791227 696197926146911803186841)
          ·
            refine ⟨522148444610183852390131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 696197926146911803186841 522148444610183852390131)
            ·
              refine ⟨783222666915275778585197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522148444610183852390131 783222666915275778585197)
              ·
                refine ⟨293708500093228416969449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 783222666915275778585197 293708500093228416969449)
                ·
                  refine ⟨220281375069921312727087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293708500093228416969449 220281375069921312727087)
                  ·
                    rfl

theorem cell20_482621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_482621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482621 prefixEnd_482621 := by exact prefixLift 482621
  have htrace : WordTrace (prefixWord ++ tailWord_482621) baseStart_482621 baseEnd_482621 := by
    simpa [prefixWord, tailWord_482621, baseEnd_482621] using wordTrace_append hprefix tailTrace_482621
  have hstable : (prefixWord ++ tailWord_482621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482621).length < 2 ^ (prefixWord ++ tailWord_482621).sum := by decide
  have hdescent : baseEnd_482621 < baseStart_482621 := by decide
  rcases family_descends (prefixWord ++ tailWord_482621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482622 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_482622 : Nat := 118140960795 + 482622 * 2 ^ 59
def prefixEnd_482622 : Nat := 4983230072969 + 3 ^ 40 * 482622 * 2
def baseEnd_482622 : Nat := 220281831497169753693749

theorem tailTrace_482622 : CollatzResearch.WordTrace tailWord_482622 prefixEnd_482622 220281831497169753693749 := by
  unfold tailWord_482622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2200333807193799265062265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11735113638366929413665413 2200333807193799265062265)
  ·
    refine ⟨1650250355395349448796699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2200333807193799265062265 1650250355395349448796699)
    ·
      refine ⟨2475375533093024173195049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1650250355395349448796699 2475375533093024173195049)
      ·
        refine ⟨1856531649819768129896287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2475375533093024173195049 1856531649819768129896287)
        ·
          refine ⟨2784797474729652194844431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1856531649819768129896287 2784797474729652194844431)
          ·
            refine ⟨4177196212094478292266647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2784797474729652194844431 4177196212094478292266647)
            ·
              refine ⟨6265794318141717438399971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4177196212094478292266647 6265794318141717438399971)
              ·
                refine ⟨9398691477212576157599957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6265794318141717438399971 9398691477212576157599957)
                ·
                  refine ⟨220281831497169753693749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9398691477212576157599957 220281831497169753693749)
                  ·
                    rfl

theorem cell20_482622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_482622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482622 prefixEnd_482622 := by exact prefixLift 482622
  have htrace : WordTrace (prefixWord ++ tailWord_482622) baseStart_482622 baseEnd_482622 := by
    simpa [prefixWord, tailWord_482622, baseEnd_482622] using wordTrace_append hprefix tailTrace_482622
  have hstable : (prefixWord ++ tailWord_482622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482622).length < 2 ^ (prefixWord ++ tailWord_482622).sum := by decide
  have hdescent : baseEnd_482622 < baseStart_482622 := by decide
  rcases family_descends (prefixWord ++ tailWord_482622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482636 : List Nat := [2, 2, 1, 3, 2, 2, 8]
def baseStart_482636 : Nat := 118140960795 + 482636 * 2 ^ 59
def prefixEnd_482636 : Nat := 4983230072969 + 3 ^ 40 * 482636 * 2
def baseEnd_482636 : Nat := 24476469053183103025225

theorem tailTrace_482636 : CollatzResearch.WordTrace tailWord_482636 prefixEnd_482636 24476469053183103025225 := by
  unfold tailWord_482636
  simp only [CollatzResearch.WordTrace]
  refine ⟨8801590539749837255753881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11735454052999783007671841 8801590539749837255753881)
  ·
    refine ⟨6601192904812377941815411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8801590539749837255753881 6601192904812377941815411)
    ·
      refine ⟨9901789357218566912723117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6601192904812377941815411 9901789357218566912723117)
      ·
        refine ⟨3713171008956962592271169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9901789357218566912723117 3713171008956962592271169)
        ·
          refine ⟨2784878256717721944203377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3713171008956962592271169 2784878256717721944203377)
          ·
            refine ⟨2088658692538291458152533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2784878256717721944203377 2088658692538291458152533)
            ·
              refine ⟨24476469053183103025225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2088658692538291458152533 24476469053183103025225)
              ·
                rfl

theorem cell20_482636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 8].length) (baseStart_482636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482636 prefixEnd_482636 := by exact prefixLift 482636
  have htrace : WordTrace (prefixWord ++ tailWord_482636) baseStart_482636 baseEnd_482636 := by
    simpa [prefixWord, tailWord_482636, baseEnd_482636] using wordTrace_append hprefix tailTrace_482636
  have hstable : (prefixWord ++ tailWord_482636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482636).length < 2 ^ (prefixWord ++ tailWord_482636).sum := by decide
  have hdescent : baseEnd_482636 < baseStart_482636 := by decide
  rcases family_descends (prefixWord ++ tailWord_482636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482643 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 5]
def baseStart_482643 : Nat := 118140960795 + 482643 * 2 ^ 59
def prefixEnd_482643 : Nat := 4983230072969 + 3 ^ 40 * 482643 * 2
def baseEnd_482643 : Nat := 220291416469387013993663

theorem tailTrace_482643 : CollatzResearch.WordTrace tailWord_482643 prefixEnd_482643 220291416469387013993663 := by
  unfold tailWord_482643
  simp only [CollatzResearch.WordTrace]
  refine ⟨17603436390474314707012583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11735624260316209804675055 17603436390474314707012583)
  ·
    refine ⟨26405154585711472060518875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17603436390474314707012583 26405154585711472060518875)
    ·
      refine ⟨39607731878567208090778313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26405154585711472060518875 39607731878567208090778313)
      ·
        refine ⟨29705798908925406068083735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39607731878567208090778313 29705798908925406068083735)
        ·
          refine ⟨44558698363388109102125603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29705798908925406068083735 44558698363388109102125603)
          ·
            refine ⟨66838047545082163653188405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44558698363388109102125603 66838047545082163653188405)
            ·
              refine ⟨6266066957351452842486413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66838047545082163653188405 6266066957351452842486413)
              ·
                refine ⟨2349775109006794815932405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6266066957351452842486413 2349775109006794815932405)
                ·
                  refine ⟨220291416469387013993663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2349775109006794815932405 220291416469387013993663)
                  ·
                    rfl

theorem cell20_482643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_482643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482643 prefixEnd_482643 := by exact prefixLift 482643
  have htrace : WordTrace (prefixWord ++ tailWord_482643) baseStart_482643 baseEnd_482643 := by
    simpa [prefixWord, tailWord_482643, baseEnd_482643] using wordTrace_append hprefix tailTrace_482643
  have hstable : (prefixWord ++ tailWord_482643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482643).length < 2 ^ (prefixWord ++ tailWord_482643).sum := by decide
  have hdescent : baseEnd_482643 < baseStart_482643 := by decide
  rcases family_descends (prefixWord ++ tailWord_482643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482656 : List Nat := [2, 1, 1, 3, 4, 3, 2, 1, 3]
def baseStart_482656 : Nat := 118140960795 + 482656 * 2 ^ 59
def prefixEnd_482656 : Nat := 4983230072969 + 3 ^ 40 * 482656 * 2
def baseEnd_482656 : Nat := 220297350023616746560277

theorem tailTrace_482656 : CollatzResearch.WordTrace tailWord_482656 prefixEnd_482656 220297350023616746560277 := by
  unfold tailWord_482656
  simp only [CollatzResearch.WordTrace]
  refine ⟨8801955269713608963617911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11735940359618145284823881 8801955269713608963617911)
  ·
    refine ⟨13202932904570413445426867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8801955269713608963617911 13202932904570413445426867)
    ·
      refine ⟨19804399356855620168140301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13202932904570413445426867 19804399356855620168140301)
      ·
        refine ⟨7426649758820857563052613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19804399356855620168140301 7426649758820857563052613)
        ·
          refine ⟨1392496829778910793072365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7426649758820857563052613 1392496829778910793072365)
          ·
            refine ⟨522186311167091547402137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1392496829778910793072365 522186311167091547402137)
            ·
              refine ⟨391639733375318660551603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522186311167091547402137 391639733375318660551603)
              ·
                refine ⟨587459600062977990827405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391639733375318660551603 587459600062977990827405)
                ·
                  refine ⟨220297350023616746560277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 587459600062977990827405 220297350023616746560277)
                  ·
                    rfl

theorem cell20_482656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 3].length) (baseStart_482656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482656 prefixEnd_482656 := by exact prefixLift 482656
  have htrace : WordTrace (prefixWord ++ tailWord_482656) baseStart_482656 baseEnd_482656 := by
    simpa [prefixWord, tailWord_482656, baseEnd_482656] using wordTrace_append hprefix tailTrace_482656
  have hstable : (prefixWord ++ tailWord_482656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482656).length < 2 ^ (prefixWord ++ tailWord_482656).sum := by decide
  have hdescent : baseEnd_482656 < baseStart_482656 := by decide
  rcases family_descends (prefixWord ++ tailWord_482656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482674 : List Nat := [3, 2, 1, 2, 1, 2, 1, 8]
def baseStart_482674 : Nat := 118140960795 + 482674 * 2 ^ 59
def prefixEnd_482674 : Nat := 4983230072969 + 3 ^ 40 * 482674 * 2
def baseEnd_482674 : Nat := 73435188571362894653401

theorem tailTrace_482674 : CollatzResearch.WordTrace tailWord_482674 prefixEnd_482674 73435188571362894653401 := by
  unfold tailWord_482674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4401141763340501750347769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11736378035574671334260717 4401141763340501750347769)
  ·
    refine ⟨3300856322505376312760827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4401141763340501750347769 3300856322505376312760827)
    ·
      refine ⟨4951284483758064469141241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3300856322505376312760827 4951284483758064469141241)
      ·
        refine ⟨3713463362818548351855931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4951284483758064469141241 3713463362818548351855931)
        ·
          refine ⟨5570195044227822527783897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3713463362818548351855931 5570195044227822527783897)
          ·
            refine ⟨4177646283170866895837923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5570195044227822527783897 4177646283170866895837923)
            ·
              refine ⟨6266469424756300343756885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4177646283170866895837923 6266469424756300343756885)
              ·
                refine ⟨73435188571362894653401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6266469424756300343756885 73435188571362894653401)
                ·
                  rfl

theorem cell20_482674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_482674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482674 prefixEnd_482674 := by exact prefixLift 482674
  have htrace : WordTrace (prefixWord ++ tailWord_482674) baseStart_482674 baseEnd_482674 := by
    simpa [prefixWord, tailWord_482674, baseEnd_482674] using wordTrace_append hprefix tailTrace_482674
  have hstable : (prefixWord ++ tailWord_482674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482674).length < 2 ^ (prefixWord ++ tailWord_482674).sum := by decide
  have hdescent : baseEnd_482674 < baseStart_482674 := by decide
  rcases family_descends (prefixWord ++ tailWord_482674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482681 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 7]
def baseStart_482681 : Nat := 118140960795 + 482681 * 2 ^ 59
def prefixEnd_482681 : Nat := 4983230072969 + 3 ^ 40 * 482681 * 2
def baseEnd_482681 : Nat := 220308760704827770726841

theorem tailTrace_482681 : CollatzResearch.WordTrace tailWord_482681 prefixEnd_482681 220308760704827770726841 := by
  unfold tailWord_482681
  simp only [CollatzResearch.WordTrace]
  refine ⟨17604822364336647196895897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11736548242891098131263931 17604822364336647196895897)
  ·
    refine ⟨13203616773252485397671923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17604822364336647196895897 13203616773252485397671923)
    ·
      refine ⟨19805425159878728096507885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13203616773252485397671923 19805425159878728096507885)
      ·
        refine ⟨7427034434954523036190457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19805425159878728096507885 7427034434954523036190457)
        ·
          refine ⟨5570275826215892277142843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7427034434954523036190457 5570275826215892277142843)
          ·
            refine ⟨8355413739323838415714265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5570275826215892277142843 8355413739323838415714265)
            ·
              refine ⟨6266560304492878811785699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8355413739323838415714265 6266560304492878811785699)
              ·
                refine ⟨9399840456739318217678549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6266560304492878811785699 9399840456739318217678549)
                ·
                  refine ⟨220308760704827770726841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9399840456739318217678549 220308760704827770726841)
                  ·
                    rfl

theorem cell20_482681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_482681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482681 prefixEnd_482681 := by exact prefixLift 482681
  have htrace : WordTrace (prefixWord ++ tailWord_482681) baseStart_482681 baseEnd_482681 := by
    simpa [prefixWord, tailWord_482681, baseEnd_482681] using wordTrace_append hprefix tailTrace_482681
  have hstable : (prefixWord ++ tailWord_482681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482681).length < 2 ^ (prefixWord ++ tailWord_482681).sum := by decide
  have hdescent : baseEnd_482681 < baseStart_482681 := by decide
  rcases family_descends (prefixWord ++ tailWord_482681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482684 : List Nat := [2, 2, 2, 1, 1, 1, 4, 5, 2]
def baseStart_482684 : Nat := 118140960795 + 482684 * 2 ^ 59
def prefixEnd_482684 : Nat := 4983230072969 + 3 ^ 40 * 482684 * 2
def baseEnd_482684 : Nat := 220310129986573093626829

theorem tailTrace_482684 : CollatzResearch.WordTrace tailWord_482684 prefixEnd_482684 220310129986573093626829 := by
  unfold tailWord_482684
  simp only [CollatzResearch.WordTrace]
  refine ⟨8802465891662889354627553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11736621188883852472836737 8802465891662889354627553)
  ·
    refine ⟨6601849418747167015970665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8802465891662889354627553 6601849418747167015970665)
    ·
      refine ⟨4951387064060375261977999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6601849418747167015970665 4951387064060375261977999)
      ·
        refine ⟨7427080596090562892966999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4951387064060375261977999 7427080596090562892966999)
        ·
          refine ⟨11140620894135844339450499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7427080596090562892966999 11140620894135844339450499)
          ·
            refine ⟨16710931341203766509175749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11140620894135844339450499 16710931341203766509175749)
            ·
              refine ⟨3133299626475706220470453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16710931341203766509175749 3133299626475706220470453)
              ·
                refine ⟨293746839982097458169105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3133299626475706220470453 293746839982097458169105)
                ·
                  refine ⟨220310129986573093626829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293746839982097458169105 220310129986573093626829)
                  ·
                    rfl

theorem cell20_482684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_482684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482684 prefixEnd_482684 := by exact prefixLift 482684
  have htrace : WordTrace (prefixWord ++ tailWord_482684) baseStart_482684 baseEnd_482684 := by
    simpa [prefixWord, tailWord_482684, baseEnd_482684] using wordTrace_append hprefix tailTrace_482684
  have hstable : (prefixWord ++ tailWord_482684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482684).length < 2 ^ (prefixWord ++ tailWord_482684).sum := by decide
  have hdescent : baseEnd_482684 < baseStart_482684 := by decide
  rcases family_descends (prefixWord ++ tailWord_482684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482697 : List Nat := [1, 2, 1, 1, 8, 1, 2, 2, 2]
def baseStart_482697 : Nat := 118140960795 + 482697 * 2 ^ 59
def prefixEnd_482697 : Nat := 4983230072969 + 3 ^ 40 * 482697 * 2
def baseEnd_482697 : Nat := 220316063540802826193443

theorem tailTrace_482697 : CollatzResearch.WordTrace tailWord_482697 prefixEnd_482697 220316063540802826193443 := by
  unfold tailWord_482697
  simp only [CollatzResearch.WordTrace]
  refine ⟨17605405932278681929478345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11736937288185787952985563 17605405932278681929478345)
  ·
    refine ⟨13204054449209011447108759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17605405932278681929478345 13204054449209011447108759)
    ·
      refine ⟨19806081673813517170663139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13204054449209011447108759 19806081673813517170663139)
      ·
        refine ⟨29709122510720275755994709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19806081673813517170663139 29709122510720275755994709)
        ·
          refine ⟨348153779422503231515563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 29709122510720275755994709 348153779422503231515563)
          ·
            refine ⟨522230669133754847273345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348153779422503231515563 522230669133754847273345)
            ·
              refine ⟨391673001850316135455009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522230669133754847273345 391673001850316135455009)
              ·
                refine ⟨293754751387737101591257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391673001850316135455009 293754751387737101591257)
                ·
                  refine ⟨220316063540802826193443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293754751387737101591257 220316063540802826193443)
                  ·
                    rfl

theorem cell20_482697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 2].length) (baseStart_482697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482697 prefixEnd_482697 := by exact prefixLift 482697
  have htrace : WordTrace (prefixWord ++ tailWord_482697) baseStart_482697 baseEnd_482697 := by
    simpa [prefixWord, tailWord_482697, baseEnd_482697] using wordTrace_append hprefix tailTrace_482697
  have hstable : (prefixWord ++ tailWord_482697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482697).length < 2 ^ (prefixWord ++ tailWord_482697).sum := by decide
  have hdescent : baseEnd_482697 < baseStart_482697 := by decide
  rcases family_descends (prefixWord ++ tailWord_482697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482708 : List Nat := [2, 4, 2, 1, 2, 3, 1, 5]
def baseStart_482708 : Nat := 118140960795 + 482708 * 2 ^ 59
def prefixEnd_482708 : Nat := 4983230072969 + 3 ^ 40 * 482708 * 2
def baseEnd_482708 : Nat := 73440361413511892275577

theorem tailTrace_482708 : CollatzResearch.WordTrace tailWord_482708 prefixEnd_482708 73440361413511892275577 := by
  unfold tailWord_482708
  simp only [CollatzResearch.WordTrace]
  refine ⟨8802903567619415404064389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11737204756825887205419185 8802903567619415404064389)
  ·
    refine ⟨1650544418928640388262073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8802903567619415404064389 1650544418928640388262073)
    ·
      refine ⟨1237908314196480291196555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1650544418928640388262073 1237908314196480291196555)
      ·
        refine ⟨1856862471294720436794833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1237908314196480291196555 1856862471294720436794833)
        ·
          refine ⟨1392646853471040327596125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1856862471294720436794833 1392646853471040327596125)
          ·
            refine ⟨522242570051640122848547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1392646853471040327596125 522242570051640122848547)
            ·
              refine ⟨783363855077460184272821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522242570051640122848547 783363855077460184272821)
              ·
                refine ⟨73440361413511892275577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 783363855077460184272821 73440361413511892275577)
                ·
                  rfl

theorem cell20_482708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_482708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482708 prefixEnd_482708 := by exact prefixLift 482708
  have htrace : WordTrace (prefixWord ++ tailWord_482708) baseStart_482708 baseEnd_482708 := by
    simpa [prefixWord, tailWord_482708, baseEnd_482708] using wordTrace_append hprefix tailTrace_482708
  have hstable : (prefixWord ++ tailWord_482708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482708).length < 2 ^ (prefixWord ++ tailWord_482708).sum := by decide
  have hdescent : baseEnd_482708 < baseStart_482708 := by decide
  rcases family_descends (prefixWord ++ tailWord_482708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482722 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_482722 : Nat := 118140960795 + 482722 * 2 ^ 59
def prefixEnd_482722 : Nat := 4983230072969 + 3 ^ 40 * 482722 * 2
def baseEnd_482722 : Nat := 220327474222013850360007

theorem tailTrace_482722 : CollatzResearch.WordTrace tailWord_482722 prefixEnd_482722 220327474222013850360007 := by
  unfold tailWord_482722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4401579439297027799784605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11737545171458740799425613 4401579439297027799784605)
  ·
    refine ⟨1650592289736385424919227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4401579439297027799784605 1650592289736385424919227)
    ·
      refine ⟨2475888434604578137378841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1650592289736385424919227 2475888434604578137378841)
      ·
        refine ⟨1856916325953433603034131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2475888434604578137378841 1856916325953433603034131)
        ·
          refine ⟨2785374488930150404551197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1856916325953433603034131 2785374488930150404551197)
          ·
            refine ⟨1044515433348806401706699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2785374488930150404551197 1044515433348806401706699)
            ·
              refine ⟨1566773150023209602560049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044515433348806401706699 1566773150023209602560049)
              ·
                refine ⟨1175079862517407201920037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1566773150023209602560049 1175079862517407201920037)
                ·
                  refine ⟨220327474222013850360007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1175079862517407201920037 220327474222013850360007)
                  ·
                    rfl

theorem cell20_482722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_482722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482722 prefixEnd_482722 := by exact prefixLift 482722
  have htrace : WordTrace (prefixWord ++ tailWord_482722) baseStart_482722 baseEnd_482722 := by
    simpa [prefixWord, tailWord_482722, baseEnd_482722] using wordTrace_append hprefix tailTrace_482722
  have hstable : (prefixWord ++ tailWord_482722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482722).length < 2 ^ (prefixWord ++ tailWord_482722).sum := by decide
  have hdescent : baseEnd_482722 < baseStart_482722 := by decide
  rcases family_descends (prefixWord ++ tailWord_482722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482760 : List Nat := [2, 1, 3, 1, 3, 1, 1, 6, 2]
def baseStart_482760 : Nat := 118140960795 + 482760 * 2 ^ 59
def prefixEnd_482760 : Nat := 4983230072969 + 3 ^ 40 * 482760 * 2
def baseEnd_482760 : Nat := 220344818457454607093185

theorem tailTrace_482760 : CollatzResearch.WordTrace tailWord_482760 prefixEnd_482760 220344818457454607093185 := by
  unfold tailWord_482760
  simp only [CollatzResearch.WordTrace]
  refine ⟨8803851865525221844510867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11738469154033629126014489 8803851865525221844510867)
  ·
    refine ⟨13205777798287832766766301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8803851865525221844510867 13205777798287832766766301)
    ·
      refine ⟨4952166674357937287537363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13205777798287832766766301 4952166674357937287537363)
      ·
        refine ⟨7428250011536905931306045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4952166674357937287537363 7428250011536905931306045)
        ·
          refine ⟨2785593754326339724239767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7428250011536905931306045 2785593754326339724239767)
          ·
            refine ⟨4178390631489509586359651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785593754326339724239767 4178390631489509586359651)
            ·
              refine ⟨6267585947234264379539477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178390631489509586359651 6267585947234264379539477)
              ·
                refine ⟨293793091276606142790913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6267585947234264379539477 293793091276606142790913)
                ·
                  refine ⟨220344818457454607093185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293793091276606142790913 220344818457454607093185)
                  ·
                    rfl

theorem cell20_482760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 2].length) (baseStart_482760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482760 prefixEnd_482760 := by exact prefixLift 482760
  have htrace : WordTrace (prefixWord ++ tailWord_482760) baseStart_482760 baseEnd_482760 := by
    simpa [prefixWord, tailWord_482760, baseEnd_482760] using wordTrace_append hprefix tailTrace_482760
  have hstable : (prefixWord ++ tailWord_482760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482760).length < 2 ^ (prefixWord ++ tailWord_482760).sum := by decide
  have hdescent : baseEnd_482760 < baseStart_482760 := by decide
  rcases family_descends (prefixWord ++ tailWord_482760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482794 : List Nat := [3, 1, 3, 1, 4, 2, 1, 3, 2]
def baseStart_482794 : Nat := 118140960795 + 482794 * 2 ^ 59
def prefixEnd_482794 : Nat := 4983230072969 + 3 ^ 40 * 482794 * 2
def baseEnd_482794 : Nat := 220360336983901599959713

theorem tailTrace_482794 : CollatzResearch.WordTrace tailWord_482794 prefixEnd_482794 220360336983901599959713 := by
  unfold tailWord_482794
  simp only [CollatzResearch.WordTrace]
  refine ⟨4402235953231816873939859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11739295875284844997172957 4402235953231816873939859)
  ·
    refine ⟨6603353929847725310909789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4402235953231816873939859 6603353929847725310909789)
    ·
      refine ⟨2476257723692896991591171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6603353929847725310909789 2476257723692896991591171)
      ·
        refine ⟨3714386585539345487386757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2476257723692896991591171 3714386585539345487386757)
        ·
          refine ⟨696447484788627278885017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3714386585539345487386757 696447484788627278885017)
          ·
            refine ⟨522335613591470459163763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 696447484788627278885017 522335613591470459163763)
            ·
              refine ⟨783503420387205688745645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522335613591470459163763 783503420387205688745645)
              ·
                refine ⟨293813782645202133279617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 783503420387205688745645 293813782645202133279617)
                ·
                  refine ⟨220360336983901599959713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293813782645202133279617 220360336983901599959713)
                  ·
                    rfl

theorem cell20_482794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_482794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482794 prefixEnd_482794 := by exact prefixLift 482794
  have htrace : WordTrace (prefixWord ++ tailWord_482794) baseStart_482794 baseEnd_482794 := by
    simpa [prefixWord, tailWord_482794, baseEnd_482794] using wordTrace_append hprefix tailTrace_482794
  have hstable : (prefixWord ++ tailWord_482794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482794).length < 2 ^ (prefixWord ++ tailWord_482794).sum := by decide
  have hdescent : baseEnd_482794 < baseStart_482794 := by decide
  rcases family_descends (prefixWord ++ tailWord_482794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482805 : List Nat := [1, 3, 5, 1, 1, 1, 8]
def baseStart_482805 : Nat := 118140960795 + 482805 * 2 ^ 59
def prefixEnd_482805 : Nat := 4983230072969 + 3 ^ 40 * 482805 * 2
def baseEnd_482805 : Nat := 24485039742626050065889

theorem tailTrace_482805 : CollatzResearch.WordTrace tailWord_482805 prefixEnd_482805 24485039742626050065889 := by
  unfold tailWord_482805
  simp only [CollatzResearch.WordTrace]
  refine ⟨17609345015887416374409869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11739563343924944249606579 17609345015887416374409869)
  ·
    refine ⟨6603504380957781140403701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17609345015887416374409869 6603504380957781140403701)
    ·
      refine ⟨619078535714791981912847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6603504380957781140403701 619078535714791981912847)
      ·
        refine ⟨928617803572187972869271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619078535714791981912847 928617803572187972869271)
        ·
          refine ⟨1392926705358281959303907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928617803572187972869271 1392926705358281959303907)
          ·
            refine ⟨2089390058037422938955861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1392926705358281959303907 2089390058037422938955861)
            ·
              refine ⟨24485039742626050065889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2089390058037422938955861 24485039742626050065889)
              ·
                rfl

theorem cell20_482805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 8].length) (baseStart_482805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482805 prefixEnd_482805 := by exact prefixLift 482805
  have htrace : WordTrace (prefixWord ++ tailWord_482805) baseStart_482805 baseEnd_482805 := by
    simpa [prefixWord, tailWord_482805, baseEnd_482805] using wordTrace_append hprefix tailTrace_482805
  have hstable : (prefixWord ++ tailWord_482805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482805).length < 2 ^ (prefixWord ++ tailWord_482805).sum := by decide
  have hdescent : baseEnd_482805 < baseStart_482805 := by decide
  rcases family_descends (prefixWord ++ tailWord_482805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482826 : List Nat := [3, 1, 2, 2, 2, 2, 1, 7]
def baseStart_482826 : Nat := 118140960795 + 482826 * 2 ^ 59
def prefixEnd_482826 : Nat := 4983230072969 + 3 ^ 40 * 482826 * 2
def baseEnd_482826 : Nat := 73458314218617236964305

theorem tailTrace_482826 : CollatzResearch.WordTrace tailWord_482826 prefixEnd_482826 73458314218617236964305 := by
  unfold tailWord_482826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4402527737202834240231083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11740073965874224640616221 4402527737202834240231083)
  ·
    refine ⟨6603791605804251360346625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4402527737202834240231083 6603791605804251360346625)
    ·
      refine ⟨4952843704353188520259969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6603791605804251360346625 4952843704353188520259969)
      ·
        refine ⟨3714632778264891390194977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4952843704353188520259969 3714632778264891390194977)
        ·
          refine ⟨2785974583698668542646233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3714632778264891390194977 2785974583698668542646233)
          ·
            refine ⟨2089480937774001406984675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2785974583698668542646233 2089480937774001406984675)
            ·
              refine ⟨3134221406661002110477013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2089480937774001406984675 3134221406661002110477013)
              ·
                refine ⟨73458314218617236964305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3134221406661002110477013 73458314218617236964305)
                ·
                  rfl

theorem cell20_482826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_482826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482826 prefixEnd_482826 := by exact prefixLift 482826
  have htrace : WordTrace (prefixWord ++ tailWord_482826) baseStart_482826 baseEnd_482826 := by
    simpa [prefixWord, tailWord_482826, baseEnd_482826] using wordTrace_append hprefix tailTrace_482826
  have hstable : (prefixWord ++ tailWord_482826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482826).length < 2 ^ (prefixWord ++ tailWord_482826).sum := by decide
  have hdescent : baseEnd_482826 < baseStart_482826 := by decide
  rcases family_descends (prefixWord ++ tailWord_482826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482870 : List Nat := [5, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_482870 : Nat := 118140960795 + 482870 * 2 ^ 59
def prefixEnd_482870 : Nat := 4983230072969 + 3 ^ 40 * 482870 * 2
def baseEnd_482870 : Nat := 220395025454783113426069

theorem tailTrace_482870 : CollatzResearch.WordTrace tailWord_482870 prefixEnd_482870 220395025454783113426069 := by
  unfold tailWord_482870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1100732235040745779720379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11741143840434621650350709 1100732235040745779720379)
  ·
    refine ⟨1651098352561118669580569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1100732235040745779720379 1651098352561118669580569)
    ·
      refine ⟨1238323764420839002185427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1651098352561118669580569 1238323764420839002185427)
      ·
        refine ⟨1857485646631258503278141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1238323764420839002185427 1857485646631258503278141)
        ·
          refine ⟨696557117486721938729303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1857485646631258503278141 696557117486721938729303)
          ·
            refine ⟨1044835676230082908093955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696557117486721938729303 1044835676230082908093955)
            ·
              refine ⟨1567253514345124362140933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044835676230082908093955 1567253514345124362140933)
              ·
                refine ⟨293860033939710817901425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1567253514345124362140933 293860033939710817901425)
                ·
                  refine ⟨220395025454783113426069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293860033939710817901425 220395025454783113426069)
                  ·
                    rfl

theorem cell20_482870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_482870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482870 prefixEnd_482870 := by exact prefixLift 482870
  have htrace : WordTrace (prefixWord ++ tailWord_482870) baseStart_482870 baseEnd_482870 := by
    simpa [prefixWord, tailWord_482870, baseEnd_482870] using wordTrace_append hprefix tailTrace_482870
  have hstable : (prefixWord ++ tailWord_482870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482870).length < 2 ^ (prefixWord ++ tailWord_482870).sum := by decide
  have hdescent : baseEnd_482870 < baseStart_482870 := by decide
  rcases family_descends (prefixWord ++ tailWord_482870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482874 : List Nat := [3, 1, 1, 1, 3, 2, 3, 4, 2]
def baseStart_482874 : Nat := 118140960795 + 482874 * 2 ^ 59
def prefixEnd_482874 : Nat := 4983230072969 + 3 ^ 40 * 482874 * 2
def baseEnd_482874 : Nat := 220396851163776877292719

theorem tailTrace_482874 : CollatzResearch.WordTrace tailWord_482874 prefixEnd_482874 220396851163776877292719 := by
  unfold tailWord_482874
  simp only [CollatzResearch.WordTrace]
  refine ⟨4402965413159360289667919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11741241101758294105781117 4402965413159360289667919)
  ·
    refine ⟨6604448119739040434501879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4402965413159360289667919 6604448119739040434501879)
    ·
      refine ⟨9906672179608560651752819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6604448119739040434501879 9906672179608560651752819)
      ·
        refine ⟨14860008269412840977629229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9906672179608560651752819 14860008269412840977629229)
        ·
          refine ⟨5572503101029815366610961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14860008269412840977629229 5572503101029815366610961)
          ·
            refine ⟨4179377325772361524958221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5572503101029815366610961 4179377325772361524958221)
            ·
              refine ⟨1567266497164635571859333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4179377325772361524958221 1567266497164635571859333)
              ·
                refine ⟨293862468218369169723625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1567266497164635571859333 293862468218369169723625)
                ·
                  refine ⟨220396851163776877292719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293862468218369169723625 220396851163776877292719)
                  ·
                    rfl

theorem cell20_482874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_482874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482874 prefixEnd_482874 := by exact prefixLift 482874
  have htrace : WordTrace (prefixWord ++ tailWord_482874) baseStart_482874 baseEnd_482874 := by
    simpa [prefixWord, tailWord_482874, baseEnd_482874] using wordTrace_append hprefix tailTrace_482874
  have hstable : (prefixWord ++ tailWord_482874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482874).length < 2 ^ (prefixWord ++ tailWord_482874).sum := by decide
  have hdescent : baseEnd_482874 < baseStart_482874 := by decide
  rcases family_descends (prefixWord ++ tailWord_482874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482967 : List Nat := [1, 1, 3, 3, 2, 4, 1, 3, 2]
def baseStart_482967 : Nat := 118140960795 + 482967 * 2 ^ 59
def prefixEnd_482967 : Nat := 4983230072969 + 3 ^ 40 * 482967 * 2
def baseEnd_482967 : Nat := 220439298897881887192339

theorem tailTrace_482967 : CollatzResearch.WordTrace tailWord_482967 prefixEnd_482967 220439298897881887192339 := by
  unfold tailWord_482967
  simp only [CollatzResearch.WordTrace]
  refine ⟨17615253641300518041807155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11743502427533678694538103 17615253641300518041807155)
  ·
    refine ⟨26422880461950777062710733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17615253641300518041807155 26422880461950777062710733)
    ·
      refine ⟨9908580173231541398516525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26422880461950777062710733 9908580173231541398516525)
      ·
        refine ⟨3715717564961828024443697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9908580173231541398516525 3715717564961828024443697)
        ·
          refine ⟨2786788173721371018332773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3715717564961828024443697 2786788173721371018332773)
          ·
            refine ⟨522522782572757065937395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2786788173721371018332773 522522782572757065937395)
            ·
              refine ⟨783784173859135598906093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522522782572757065937395 783784173859135598906093)
              ·
                refine ⟨293919065197175849589785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 783784173859135598906093 293919065197175849589785)
                ·
                  refine ⟨220439298897881887192339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293919065197175849589785 220439298897881887192339)
                  ·
                    rfl

theorem cell20_482967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 2].length) (baseStart_482967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482967 prefixEnd_482967 := by exact prefixLift 482967
  have htrace : WordTrace (prefixWord ++ tailWord_482967) baseStart_482967 baseEnd_482967 := by
    simpa [prefixWord, tailWord_482967, baseEnd_482967] using wordTrace_append hprefix tailTrace_482967
  have hstable : (prefixWord ++ tailWord_482967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482967).length < 2 ^ (prefixWord ++ tailWord_482967).sum := by decide
  have hdescent : baseEnd_482967 < baseStart_482967 := by decide
  rcases family_descends (prefixWord ++ tailWord_482967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_482998 : List Nat := [5, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_482998 : Nat := 118140960795 + 482998 * 2 ^ 59
def prefixEnd_482998 : Nat := 4983230072969 + 3 ^ 40 * 482998 * 2
def baseEnd_482998 : Nat := 220453448142583557158879

theorem tailTrace_482998 : CollatzResearch.WordTrace tailWord_482998 prefixEnd_482998 220453448142583557158879 := by
  unfold tailWord_482998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1101024019011763146011603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11744256202792140224123765 1101024019011763146011603)
  ·
    refine ⟨1651536028517644719017405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1101024019011763146011603 1651536028517644719017405)
    ·
      refine ⟨619326010694116769631527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1651536028517644719017405 619326010694116769631527)
      ·
        refine ⟨928989016041175154447291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619326010694116769631527 928989016041175154447291)
        ·
          refine ⟨1393483524061762731670937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928989016041175154447291 1393483524061762731670937)
          ·
            refine ⟨1045112643046322048753203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1393483524061762731670937 1045112643046322048753203)
            ·
              refine ⟨1567668964569483073129805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045112643046322048753203 1567668964569483073129805)
              ·
                refine ⟨587875861713556152423677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1567668964569483073129805 587875861713556152423677)
                ·
                  refine ⟨220453448142583557158879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 587875861713556152423677 220453448142583557158879)
                  ·
                    rfl

theorem cell20_482998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_482998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_482998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_482998 prefixEnd_482998 := by exact prefixLift 482998
  have htrace : WordTrace (prefixWord ++ tailWord_482998) baseStart_482998 baseEnd_482998 := by
    simpa [prefixWord, tailWord_482998, baseEnd_482998] using wordTrace_append hprefix tailTrace_482998
  have hstable : (prefixWord ++ tailWord_482998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_482998).length < 2 ^ (prefixWord ++ tailWord_482998).sum := by decide
  have hdescent : baseEnd_482998 < baseStart_482998 := by decide
  rcases family_descends (prefixWord ++ tailWord_482998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483002 : List Nat := [3, 1, 1, 1, 2, 5, 1, 3, 3]
def baseStart_483002 : Nat := 118140960795 + 483002 * 2 ^ 59
def prefixEnd_483002 : Nat := 4983230072969 + 3 ^ 40 * 483002 * 2
def baseEnd_483002 : Nat := 220455273851577321025529

theorem tailTrace_483002 : CollatzResearch.WordTrace tailWord_483002 prefixEnd_483002 220455273851577321025529 := by
  unfold tailWord_483002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4404132549043429754832815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11744353464115812679554173 4404132549043429754832815)
  ·
    refine ⟨6606198823565144632249223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4404132549043429754832815 6606198823565144632249223)
    ·
      refine ⟨9909298235347716948373835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6606198823565144632249223 9909298235347716948373835)
      ·
        refine ⟨14863947353021575422560753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9909298235347716948373835 14863947353021575422560753)
        ·
          refine ⟨11147960514766181566920565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14863947353021575422560753 11147960514766181566920565)
          ·
            refine ⟨1045121298259329521898803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11147960514766181566920565 1045121298259329521898803)
            ·
              refine ⟨1567681947388994282848205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045121298259329521898803 1567681947388994282848205)
              ·
                refine ⟨587880730270872856068077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1567681947388994282848205 587880730270872856068077)
                ·
                  refine ⟨220455273851577321025529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 587880730270872856068077 220455273851577321025529)
                  ·
                    rfl

theorem cell20_483002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_483002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483002 prefixEnd_483002 := by exact prefixLift 483002
  have htrace : WordTrace (prefixWord ++ tailWord_483002) baseStart_483002 baseEnd_483002 := by
    simpa [prefixWord, tailWord_483002, baseEnd_483002] using wordTrace_append hprefix tailTrace_483002
  have hstable : (prefixWord ++ tailWord_483002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483002).length < 2 ^ (prefixWord ++ tailWord_483002).sum := by decide
  have hdescent : baseEnd_483002 < baseStart_483002 := by decide
  rcases family_descends (prefixWord ++ tailWord_483002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483036 : List Nat := [2, 2, 5, 1, 2, 1, 2, 2, 3]
def baseStart_483036 : Nat := 118140960795 + 483036 * 2 ^ 59
def prefixEnd_483036 : Nat := 4983230072969 + 3 ^ 40 * 483036 * 2
def baseEnd_483036 : Nat := 220470792378024313892057

theorem tailTrace_483036 : CollatzResearch.WordTrace tailWord_483036 prefixEnd_483036 220470792378024313892057 := by
  unfold tailWord_483036
  simp only [CollatzResearch.WordTrace]
  refine ⟨8808885139025271413034481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11745180185367028550712641 8808885139025271413034481)
  ·
    refine ⟨6606663854268953559775861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8808885139025271413034481 6606663854268953559775861)
    ·
      refine ⟨619374736337714396228987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6606663854268953559775861 619374736337714396228987)
      ·
        refine ⟨929062104506571594343481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619374736337714396228987 929062104506571594343481)
        ·
          refine ⟨696796578379928695757611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 929062104506571594343481 696796578379928695757611)
          ·
            refine ⟨1045194867569893043636417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696796578379928695757611 1045194867569893043636417)
            ·
              refine ⟨783896150677419782727313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1045194867569893043636417 783896150677419782727313)
              ·
                refine ⟨587922113008064837045485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783896150677419782727313 587922113008064837045485)
                ·
                  refine ⟨220470792378024313892057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 587922113008064837045485 220470792378024313892057)
                  ·
                    rfl

theorem cell20_483036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_483036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483036 prefixEnd_483036 := by exact prefixLift 483036
  have htrace : WordTrace (prefixWord ++ tailWord_483036) baseStart_483036 baseEnd_483036 := by
    simpa [prefixWord, tailWord_483036, baseEnd_483036] using wordTrace_append hprefix tailTrace_483036
  have hstable : (prefixWord ++ tailWord_483036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483036).length < 2 ^ (prefixWord ++ tailWord_483036).sum := by decide
  have hdescent : baseEnd_483036 < baseStart_483036 := by decide
  rcases family_descends (prefixWord ++ tailWord_483036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483043 : List Nat := [1, 1, 1, 7, 2, 1, 1, 4, 2]
def baseStart_483043 : Nat := 118140960795 + 483043 * 2 ^ 59
def prefixEnd_483043 : Nat := 4983230072969 + 3 ^ 40 * 483043 * 2
def baseEnd_483043 : Nat := 220473987368763400658695

theorem tailTrace_483043 : CollatzResearch.WordTrace tailWord_483043 prefixEnd_483043 220473987368763400658695 := by
  unfold tailWord_483043
  simp only [CollatzResearch.WordTrace]
  refine ⟨17618025589025183021573783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11745350392683455347715855 17618025589025183021573783)
  ·
    refine ⟨26427038383537774532360675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17618025589025183021573783 26427038383537774532360675)
    ·
      refine ⟨39640557575306661798541013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26427038383537774532360675 39640557575306661798541013)
      ·
        refine ⟨929075568171249885903305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 39640557575306661798541013 929075568171249885903305)
        ·
          refine ⟨696806676128437414427479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 929075568171249885903305 696806676128437414427479)
          ·
            refine ⟨1045210014192656121641219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696806676128437414427479 1045210014192656121641219)
            ·
              refine ⟨1567815021288984182461829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045210014192656121641219 1567815021288984182461829)
              ·
                refine ⟨293965316491684534211593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1567815021288984182461829 293965316491684534211593)
                ·
                  refine ⟨220473987368763400658695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293965316491684534211593 220473987368763400658695)
                  ·
                    rfl

theorem cell20_483043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 2].length) (baseStart_483043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483043 prefixEnd_483043 := by exact prefixLift 483043
  have htrace : WordTrace (prefixWord ++ tailWord_483043) baseStart_483043 baseEnd_483043 := by
    simpa [prefixWord, tailWord_483043, baseEnd_483043] using wordTrace_append hprefix tailTrace_483043
  have hstable : (prefixWord ++ tailWord_483043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483043).length < 2 ^ (prefixWord ++ tailWord_483043).sum := by decide
  have hdescent : baseEnd_483043 < baseStart_483043 := by decide
  rcases family_descends (prefixWord ++ tailWord_483043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483075 : List Nat := [1, 1, 1, 3, 2, 2, 2, 8]
def baseStart_483075 : Nat := 118140960795 + 483075 * 2 ^ 59
def prefixEnd_483075 : Nat := 4983230072969 + 3 ^ 40 * 483075 * 2
def baseEnd_483075 : Nat := 73496197680237837197299

theorem tailTrace_483075 : CollatzResearch.WordTrace tailWord_483075 prefixEnd_483075 73496197680237837197299 := by
  unfold tailWord_483075
  simp only [CollatzResearch.WordTrace]
  refine ⟨17619192724909252486738679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11746128483272834991159119 17619192724909252486738679)
  ·
    refine ⟨26428789087363878730108019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17619192724909252486738679 26428789087363878730108019)
    ·
      refine ⟨39643183631045818095162029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26428789087363878730108019 39643183631045818095162029)
      ·
        refine ⟨14866193861642181785685761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39643183631045818095162029 14866193861642181785685761)
        ·
          refine ⟨11149645396231636339264321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14866193861642181785685761 11149645396231636339264321)
          ·
            refine ⟨8362234047173727254448241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11149645396231636339264321 8362234047173727254448241)
            ·
              refine ⟨6271675535380295440836181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8362234047173727254448241 6271675535380295440836181)
              ·
                refine ⟨73496197680237837197299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6271675535380295440836181 73496197680237837197299)
                ·
                  rfl

theorem cell20_483075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 8].length) (baseStart_483075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483075 prefixEnd_483075 := by exact prefixLift 483075
  have htrace : WordTrace (prefixWord ++ tailWord_483075) baseStart_483075 baseEnd_483075 := by
    simpa [prefixWord, tailWord_483075, baseEnd_483075] using wordTrace_append hprefix tailTrace_483075
  have hstable : (prefixWord ++ tailWord_483075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483075).length < 2 ^ (prefixWord ++ tailWord_483075).sum := by decide
  have hdescent : baseEnd_483075 < baseStart_483075 := by decide
  rcases family_descends (prefixWord ++ tailWord_483075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483095 : List Nat := [1, 1, 3, 4, 2, 3, 1, 2, 3]
def baseStart_483095 : Nat := 118140960795 + 483095 * 2 ^ 59
def prefixEnd_483095 : Nat := 4983230072969 + 3 ^ 40 * 483095 * 2
def baseEnd_483095 : Nat := 220497721585682330925149

theorem tailTrace_483095 : CollatzResearch.WordTrace tailWord_483095 prefixEnd_483095 220497721585682330925149 := by
  unfold tailWord_483095
  simp only [CollatzResearch.WordTrace]
  refine ⟨17619922184836795902466739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11746614789891197268311159 17619922184836795902466739)
  ·
    refine ⟨26429883277255193853700109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17619922184836795902466739 26429883277255193853700109)
    ·
      refine ⟨9911206228970697695137541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26429883277255193853700109 9911206228970697695137541)
      ·
        refine ⟨1858351167932005817838289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9911206228970697695137541 1858351167932005817838289)
        ·
          refine ⟨1393763375949004363378717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1858351167932005817838289 1393763375949004363378717)
          ·
            refine ⟨522661265980876636267019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1393763375949004363378717 522661265980876636267019)
            ·
              refine ⟨783991898971314954400529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522661265980876636267019 783991898971314954400529)
              ·
                refine ⟨587993924228486215800397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783991898971314954400529 587993924228486215800397)
                ·
                  refine ⟨220497721585682330925149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 587993924228486215800397 220497721585682330925149)
                  ·
                    rfl

theorem cell20_483095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 3].length) (baseStart_483095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483095 prefixEnd_483095 := by exact prefixLift 483095
  have htrace : WordTrace (prefixWord ++ tailWord_483095) baseStart_483095 baseEnd_483095 := by
    simpa [prefixWord, tailWord_483095, baseEnd_483095] using wordTrace_append hprefix tailTrace_483095
  have hstable : (prefixWord ++ tailWord_483095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483095).length < 2 ^ (prefixWord ++ tailWord_483095).sum := by decide
  have hdescent : baseEnd_483095 < baseStart_483095 := by decide
  rcases family_descends (prefixWord ++ tailWord_483095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483126 : List Nat := [5, 1, 2, 2, 1, 1, 4, 4]
def baseStart_483126 : Nat := 118140960795 + 483126 * 2 ^ 59
def prefixEnd_483126 : Nat := 4983230072969 + 3 ^ 40 * 483126 * 2
def baseEnd_483126 : Nat := 73503956943461333630563

theorem tailTrace_483126 : CollatzResearch.WordTrace tailWord_483126 prefixEnd_483126 73503956943461333630563 := by
  unfold tailWord_483126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1101315802982780512302827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11747368565149658797896821 1101315802982780512302827)
  ·
    refine ⟨1651973704474170768454241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1101315802982780512302827 1651973704474170768454241)
    ·
      refine ⟨1238980278355628076340681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1651973704474170768454241 1238980278355628076340681)
      ·
        refine ⟨929235208766721057255511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1238980278355628076340681 929235208766721057255511)
        ·
          refine ⟨1393852813150081585883267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929235208766721057255511 1393852813150081585883267)
          ·
            refine ⟨2090779219725122378824901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1393852813150081585883267 2090779219725122378824901)
            ·
              refine ⟨392021103698460446029669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2090779219725122378824901 392021103698460446029669)
              ·
                refine ⟨73503956943461333630563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 392021103698460446029669 73503956943461333630563)
                ·
                  rfl

theorem cell20_483126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_483126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483126 prefixEnd_483126 := by exact prefixLift 483126
  have htrace : WordTrace (prefixWord ++ tailWord_483126) baseStart_483126 baseEnd_483126 := by
    simpa [prefixWord, tailWord_483126, baseEnd_483126] using wordTrace_append hprefix tailTrace_483126
  have hstable : (prefixWord ++ tailWord_483126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483126).length < 2 ^ (prefixWord ++ tailWord_483126).sum := by decide
  have hdescent : baseEnd_483126 < baseStart_483126 := by decide
  rcases family_descends (prefixWord ++ tailWord_483126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483130 : List Nat := [3, 1, 1, 1, 5, 2, 1, 6]
def baseStart_483130 : Nat := 118140960795 + 483130 * 2 ^ 59
def prefixEnd_483130 : Nat := 4983230072969 + 3 ^ 40 * 483130 * 2
def baseEnd_483130 : Nat := 73504565513125921586113

theorem tailTrace_483130 : CollatzResearch.WordTrace tailWord_483130 prefixEnd_483130 73504565513125921586113 := by
  unfold tailWord_483130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4405299684927499219997711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11747465826473331253327229 4405299684927499219997711)
  ·
    refine ⟨6607949527391248829996567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4405299684927499219997711 6607949527391248829996567)
    ·
      refine ⟨9911924291086873244994851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6607949527391248829996567 9911924291086873244994851)
      ·
        refine ⟨14867886436630309867492277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9911924291086873244994851 14867886436630309867492277)
        ·
          refine ⟨1393864353434091550077401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14867886436630309867492277 1393864353434091550077401)
          ·
            refine ⟨1045398265075568662558051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1393864353434091550077401 1045398265075568662558051)
            ·
              refine ⟨1568097397613352993837077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045398265075568662558051 1568097397613352993837077)
              ·
                refine ⟨73504565513125921586113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1568097397613352993837077 73504565513125921586113)
                ·
                  rfl

theorem cell20_483130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_483130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483130 prefixEnd_483130 := by exact prefixLift 483130
  have htrace : WordTrace (prefixWord ++ tailWord_483130) baseStart_483130 baseEnd_483130 := by
    simpa [prefixWord, tailWord_483130, baseEnd_483130] using wordTrace_append hprefix tailTrace_483130
  have hstable : (prefixWord ++ tailWord_483130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483130).length < 2 ^ (prefixWord ++ tailWord_483130).sum := by decide
  have hdescent : baseEnd_483130 < baseStart_483130 := by decide
  rcases family_descends (prefixWord ++ tailWord_483130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483157 : List Nat := [1, 3, 2, 2, 2, 3, 3, 2, 2]
def baseStart_483157 : Nat := 118140960795 + 483157 * 2 ^ 59
def prefixEnd_483157 : Nat := 4983230072969 + 3 ^ 40 * 483157 * 2
def baseEnd_483157 : Nat := 220526020075085670858229

theorem tailTrace_483157 : CollatzResearch.WordTrace tailWord_483157 prefixEnd_483157 220526020075085670858229 := by
  unfold tailWord_483157
  simp only [CollatzResearch.WordTrace]
  refine ⟨17622183510612180491223725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11748122340408120327482483 17622183510612180491223725)
  ·
    refine ⟨6608318816479567684208897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17622183510612180491223725 6608318816479567684208897)
    ·
      refine ⟨4956239112359675763156673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6608318816479567684208897 4956239112359675763156673)
      ·
        refine ⟨3717179334269756822367505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4956239112359675763156673 3717179334269756822367505)
        ·
          refine ⟨2787884500702317616775629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3717179334269756822367505 2787884500702317616775629)
          ·
            refine ⟨1045456687763369106290861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2787884500702317616775629 1045456687763369106290861)
            ·
              refine ⟨392046257911263414859073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1045456687763369106290861 392046257911263414859073)
              ·
                refine ⟨294034693433447561144305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392046257911263414859073 294034693433447561144305)
                ·
                  refine ⟨220526020075085670858229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294034693433447561144305 220526020075085670858229)
                  ·
                    rfl

theorem cell20_483157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_483157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483157 prefixEnd_483157 := by exact prefixLift 483157
  have htrace : WordTrace (prefixWord ++ tailWord_483157) baseStart_483157 baseEnd_483157 := by
    simpa [prefixWord, tailWord_483157, baseEnd_483157] using wordTrace_append hprefix tailTrace_483157
  have hstable : (prefixWord ++ tailWord_483157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483157).length < 2 ^ (prefixWord ++ tailWord_483157).sum := by decide
  have hdescent : baseEnd_483157 < baseStart_483157 := by decide
  rcases family_descends (prefixWord ++ tailWord_483157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483168 : List Nat := [2, 1, 1, 3, 3, 3, 2, 5]
def baseStart_483168 : Nat := 118140960795 + 483168 * 2 ^ 59
def prefixEnd_483168 : Nat := 4983230072969 + 3 ^ 40 * 483168 * 2
def baseEnd_483168 : Nat := 73510346924939507163839

theorem tailTrace_483168 : CollatzResearch.WordTrace tailWord_483168 prefixEnd_483168 73510346924939507163839 := by
  unfold tailWord_483168
  simp only [CollatzResearch.WordTrace]
  refine ⟨8811292356786164684937079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11748389809048219579916105 8811292356786164684937079)
  ·
    refine ⟨13216938535179247027405619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8811292356786164684937079 13216938535179247027405619)
    ·
      refine ⟨19825407802768870541108429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13216938535179247027405619 19825407802768870541108429)
      ·
        refine ⟨7434527926038326452915661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19825407802768870541108429 7434527926038326452915661)
        ·
          refine ⟨2787947972264372419843373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7434527926038326452915661 2787947972264372419843373)
          ·
            refine ⟨1045480489599139657441265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2787947972264372419843373 1045480489599139657441265)
            ·
              refine ⟨784110367199354743080949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1045480489599139657441265 784110367199354743080949)
              ·
                refine ⟨73510346924939507163839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 784110367199354743080949 73510346924939507163839)
                ·
                  rfl

theorem cell20_483168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_483168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483168 prefixEnd_483168 := by exact prefixLift 483168
  have htrace : WordTrace (prefixWord ++ tailWord_483168) baseStart_483168 baseEnd_483168 := by
    simpa [prefixWord, tailWord_483168, baseEnd_483168] using wordTrace_append hprefix tailTrace_483168
  have hstable : (prefixWord ++ tailWord_483168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483168).length < 2 ^ (prefixWord ++ tailWord_483168).sum := by decide
  have hdescent : baseEnd_483168 < baseStart_483168 := by decide
  rcases family_descends (prefixWord ++ tailWord_483168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483199 : List Nat := [1, 1, 2, 2, 1, 1, 3, 7, 2]
def baseStart_483199 : Nat := 118140960795 + 483199 * 2 ^ 59
def prefixEnd_483199 : Nat := 4983230072969 + 3 ^ 40 * 483199 * 2
def baseEnd_483199 : Nat := 220545190019520191458057

theorem tailTrace_483199 : CollatzResearch.WordTrace tailWord_483199 prefixEnd_483199 220545190019520191458057 := by
  unfold tailWord_483199
  simp only [CollatzResearch.WordTrace]
  refine ⟨17623715376460021664252651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11749143584306681109501767 17623715376460021664252651)
  ·
    refine ⟨26435573064690032496378977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17623715376460021664252651 26435573064690032496378977)
    ·
      refine ⟨19826679798517524372284233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26435573064690032496378977 19826679798517524372284233)
      ·
        refine ⟨14870009848888143279213175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19826679798517524372284233 14870009848888143279213175)
        ·
          refine ⟨22305014773332214918819763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14870009848888143279213175 22305014773332214918819763)
          ·
            refine ⟨33457522159998322378229645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22305014773332214918819763 33457522159998322378229645)
            ·
              refine ⟨12546570809999370891836117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33457522159998322378229645 12546570809999370891836117)
              ·
                refine ⟨294060253359360255277409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12546570809999370891836117 294060253359360255277409)
                ·
                  refine ⟨220545190019520191458057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294060253359360255277409 220545190019520191458057)
                  ·
                    rfl

theorem cell20_483199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 2].length) (baseStart_483199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483199 prefixEnd_483199 := by exact prefixLift 483199
  have htrace : WordTrace (prefixWord ++ tailWord_483199) baseStart_483199 baseEnd_483199 := by
    simpa [prefixWord, tailWord_483199, baseEnd_483199] using wordTrace_append hprefix tailTrace_483199
  have hstable : (prefixWord ++ tailWord_483199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483199).length < 2 ^ (prefixWord ++ tailWord_483199).sum := by decide
  have hdescent : baseEnd_483199 < baseStart_483199 := by decide
  rcases family_descends (prefixWord ++ tailWord_483199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483275 : List Nat := [1, 1, 1, 1, 3, 4, 1, 6, 2]
def baseStart_483275 : Nat := 118140960795 + 483275 * 2 ^ 59
def prefixEnd_483275 : Nat := 4983230072969 + 3 ^ 40 * 483275 * 2
def baseEnd_483275 : Nat := 220579878490401704924413

theorem tailTrace_483275 : CollatzResearch.WordTrace tailWord_483275 prefixEnd_483275 220579878490401704924413 := by
  unfold tailWord_483275
  simp only [CollatzResearch.WordTrace]
  refine ⟨17626487324184686644019279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11750991549456457762679519 17626487324184686644019279)
  ·
    refine ⟨26439730986277029966028919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17626487324184686644019279 26439730986277029966028919)
    ·
      refine ⟨39659596479415544949043379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26439730986277029966028919 39659596479415544949043379)
      ·
        refine ⟨59489394719123317423565069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39659596479415544949043379 59489394719123317423565069)
        ·
          refine ⟨22308523019671244033836901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59489394719123317423565069 22308523019671244033836901)
          ·
            refine ⟨4182848066188358256344419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22308523019671244033836901 4182848066188358256344419)
            ·
              refine ⟨6274272099282537384516629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4182848066188358256344419 6274272099282537384516629)
              ·
                refine ⟨294106504653868939899217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6274272099282537384516629 294106504653868939899217)
                ·
                  refine ⟨220579878490401704924413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294106504653868939899217 220579878490401704924413)
                  ·
                    rfl

theorem cell20_483275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 2].length) (baseStart_483275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483275 prefixEnd_483275 := by exact prefixLift 483275
  have htrace : WordTrace (prefixWord ++ tailWord_483275) baseStart_483275 baseEnd_483275 := by
    simpa [prefixWord, tailWord_483275, baseEnd_483275] using wordTrace_append hprefix tailTrace_483275
  have hstable : (prefixWord ++ tailWord_483275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483275).length < 2 ^ (prefixWord ++ tailWord_483275).sum := by decide
  have hdescent : baseEnd_483275 < baseStart_483275 := by decide
  rcases family_descends (prefixWord ++ tailWord_483275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483285 : List Nat := [1, 3, 2, 3, 2, 2, 3, 1, 3]
def baseStart_483285 : Nat := 118140960795 + 483285 * 2 ^ 59
def prefixEnd_483285 : Nat := 4983230072969 + 3 ^ 40 * 483285 * 2
def baseEnd_483285 : Nat := 220584442762886114591039

theorem tailTrace_483285 : CollatzResearch.WordTrace tailWord_483285 prefixEnd_483285 220584442762886114591039 := by
  unfold tailWord_483285
  simp only [CollatzResearch.WordTrace]
  refine ⟨17626852054148458351883309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11751234702765638901255539 17626852054148458351883309)
  ·
    refine ⟨6610069520305671881956241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17626852054148458351883309 6610069520305671881956241)
    ·
      refine ⟨4957552140229253911467181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6610069520305671881956241 4957552140229253911467181)
      ·
        refine ⟨1859082052585970216800193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4957552140229253911467181 1859082052585970216800193)
        ·
          refine ⟨1394311539439477662600145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1859082052585970216800193 1394311539439477662600145)
          ·
            refine ⟨1045733654579608246950109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1394311539439477662600145 1045733654579608246950109)
            ·
              refine ⟨392150120467353092606291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1045733654579608246950109 392150120467353092606291)
              ·
                refine ⟨588225180701029638909437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392150120467353092606291 588225180701029638909437)
                ·
                  refine ⟨220584442762886114591039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 588225180701029638909437 220584442762886114591039)
                  ·
                    rfl

theorem cell20_483285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_483285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483285 prefixEnd_483285 := by exact prefixLift 483285
  have htrace : WordTrace (prefixWord ++ tailWord_483285) baseStart_483285 baseEnd_483285 := by
    simpa [prefixWord, tailWord_483285, baseEnd_483285] using wordTrace_append hprefix tailTrace_483285
  have hstable : (prefixWord ++ tailWord_483285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483285).length < 2 ^ (prefixWord ++ tailWord_483285).sum := by decide
  have hdescent : baseEnd_483285 < baseStart_483285 := by decide
  rcases family_descends (prefixWord ++ tailWord_483285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483299 : List Nat := [1, 1, 1, 6, 1, 4, 2, 4]
def baseStart_483299 : Nat := 118140960795 + 483299 * 2 ^ 59
def prefixEnd_483299 : Nat := 4983230072969 + 3 ^ 40 * 483299 * 2
def baseEnd_483299 : Nat := 73530277581454762708105

theorem tailTrace_483299 : CollatzResearch.WordTrace tailWord_483299 prefixEnd_483299 73530277581454762708105 := by
  unfold tailWord_483299
  simp only [CollatzResearch.WordTrace]
  refine ⟨17627362676097738742892951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11751575117398492495261967 17627362676097738742892951)
  ·
    refine ⟨26441044014146608114339427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17627362676097738742892951 26441044014146608114339427)
    ·
      refine ⟨39661566021219912171509141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26441044014146608114339427 39661566021219912171509141)
      ·
        refine ⟨1859135907244683383039491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39661566021219912171509141 1859135907244683383039491)
        ·
          refine ⟨2788703860867025074559237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1859135907244683383039491 2788703860867025074559237)
          ·
            refine ⟨522881973912567201479857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2788703860867025074559237 522881973912567201479857)
            ·
              refine ⟨392161480434425401109893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522881973912567201479857 392161480434425401109893)
              ·
                refine ⟨73530277581454762708105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 392161480434425401109893 73530277581454762708105)
                ·
                  rfl

theorem cell20_483299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 4].length) (baseStart_483299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483299 prefixEnd_483299 := by exact prefixLift 483299
  have htrace : WordTrace (prefixWord ++ tailWord_483299) baseStart_483299 baseEnd_483299 := by
    simpa [prefixWord, tailWord_483299, baseEnd_483299] using wordTrace_append hprefix tailTrace_483299
  have hstable : (prefixWord ++ tailWord_483299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483299).length < 2 ^ (prefixWord ++ tailWord_483299).sum := by decide
  have hdescent : baseEnd_483299 < baseStart_483299 := by decide
  rcases family_descends (prefixWord ++ tailWord_483299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483326 : List Nat := [4, 2, 2, 2, 1, 2, 3, 2, 2]
def baseStart_483326 : Nat := 118140960795 + 483326 * 2 ^ 59
def prefixEnd_483326 : Nat := 4983230072969 + 3 ^ 40 * 483326 * 2
def baseEnd_483326 : Nat := 220603156280072194224205

theorem tailTrace_483326 : CollatzResearch.WordTrace tailWord_483326 prefixEnd_483326 220603156280072194224205 := by
  unfold tailWord_483326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2203543430874990294265729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11752231631333281569417221 2203543430874990294265729)
  ·
    refine ⟨1652657573156242720699297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2203543430874990294265729 1652657573156242720699297)
    ·
      refine ⟨1239493179867182040524473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1652657573156242720699297 1239493179867182040524473)
      ·
        refine ⟨929619884900386530393355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1239493179867182040524473 929619884900386530393355)
        ·
          refine ⟨1394429827350579795590033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929619884900386530393355 1394429827350579795590033)
          ·
            refine ⟨1045822370512934846692525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1394429827350579795590033 1045822370512934846692525)
            ·
              refine ⟨392183388942350567509697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1045822370512934846692525 392183388942350567509697)
              ·
                refine ⟨294137541706762925632273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392183388942350567509697 294137541706762925632273)
                ·
                  refine ⟨220603156280072194224205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294137541706762925632273 220603156280072194224205)
                  ·
                    rfl

theorem cell20_483326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_483326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483326 prefixEnd_483326 := by exact prefixLift 483326
  have htrace : WordTrace (prefixWord ++ tailWord_483326) baseStart_483326 baseEnd_483326 := by
    simpa [prefixWord, tailWord_483326, baseEnd_483326] using wordTrace_append hprefix tailTrace_483326
  have hstable : (prefixWord ++ tailWord_483326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483326).length < 2 ^ (prefixWord ++ tailWord_483326).sum := by decide
  have hdescent : baseEnd_483326 < baseStart_483326 := by decide
  rcases family_descends (prefixWord ++ tailWord_483326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483427 : List Nat := [1, 1, 1, 5, 1, 1, 3, 5, 2]
def baseStart_483427 : Nat := 118140960795 + 483427 * 2 ^ 59
def prefixEnd_483427 : Nat := 4983230072969 + 3 ^ 40 * 483427 * 2
def baseEnd_483427 : Nat := 220649255432164731857125

theorem tailTrace_483427 : CollatzResearch.WordTrace tailWord_483427 prefixEnd_483427 220649255432164731857125 := by
  unfold tailWord_483427
  simp only [CollatzResearch.WordTrace]
  refine ⟨17632031219634016603552535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11754687479756011069035023 17632031219634016603552535)
  ·
    refine ⟨26448046829451024905328803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17632031219634016603552535 26448046829451024905328803)
    ·
      refine ⟨39672070244176537357993205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26448046829451024905328803 39672070244176537357993205)
      ·
        refine ⟨3719256585391550377311863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39672070244176537357993205 3719256585391550377311863)
        ·
          refine ⟨5578884878087325565967795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3719256585391550377311863 5578884878087325565967795)
          ·
            refine ⟨8368327317130988348951693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5578884878087325565967795 8368327317130988348951693)
            ·
              refine ⟨3138122743924120630856885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8368327317130988348951693 3138122743924120630856885)
              ·
                refine ⟨294199007242886309142833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3138122743924120630856885 294199007242886309142833)
                ·
                  refine ⟨220649255432164731857125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294199007242886309142833 220649255432164731857125)
                  ·
                    rfl

theorem cell20_483427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 2].length) (baseStart_483427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483427 prefixEnd_483427 := by exact prefixLift 483427
  have htrace : WordTrace (prefixWord ++ tailWord_483427) baseStart_483427 baseEnd_483427 := by
    simpa [prefixWord, tailWord_483427, baseEnd_483427] using wordTrace_append hprefix tailTrace_483427
  have hstable : (prefixWord ++ tailWord_483427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483427).length < 2 ^ (prefixWord ++ tailWord_483427).sum := by decide
  have hdescent : baseEnd_483427 < baseStart_483427 := by decide
  rcases family_descends (prefixWord ++ tailWord_483427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483434 : List Nat := [3, 1, 3, 2, 3, 1, 7]
def baseStart_483434 : Nat := 118140960795 + 483434 * 2 ^ 59
def prefixEnd_483434 : Nat := 4983230072969 + 3 ^ 40 * 483434 * 2
def baseEnd_483434 : Nat := 24516938935878202069307

theorem tailTrace_483434 : CollatzResearch.WordTrace tailWord_483434 prefixEnd_483434 24516938935878202069307 := by
  unfold tailWord_483434
  simp only [CollatzResearch.WordTrace]
  refine ⟨4408071632652164199764339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11754857687072437866038237 4408071632652164199764339)
  ·
    refine ⟨6612107448978246299646509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4408071632652164199764339 6612107448978246299646509)
    ·
      refine ⟨2479540293366842362367441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6612107448978246299646509 2479540293366842362367441)
      ·
        refine ⟨1859655220025131771775581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2479540293366842362367441 1859655220025131771775581)
        ·
          refine ⟨697370707509424414415843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1859655220025131771775581 697370707509424414415843)
          ·
            refine ⟨1046056061264136621623765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697370707509424414415843 1046056061264136621623765)
            ·
              refine ⟨24516938935878202069307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1046056061264136621623765 24516938935878202069307)
              ·
                rfl

theorem cell20_483434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 7].length) (baseStart_483434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483434 prefixEnd_483434 := by exact prefixLift 483434
  have htrace : WordTrace (prefixWord ++ tailWord_483434) baseStart_483434 baseEnd_483434 := by
    simpa [prefixWord, tailWord_483434, baseEnd_483434] using wordTrace_append hprefix tailTrace_483434
  have hstable : (prefixWord ++ tailWord_483434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483434).length < 2 ^ (prefixWord ++ tailWord_483434).sum := by decide
  have hdescent : baseEnd_483434 < baseStart_483434 := by decide
  rcases family_descends (prefixWord ++ tailWord_483434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483509 : List Nat := [1, 3, 3, 4, 2, 1, 2, 1, 3]
def baseStart_483509 : Nat := 118140960795 + 483509 * 2 ^ 59
def prefixEnd_483509 : Nat := 4983230072969 + 3 ^ 40 * 483509 * 2
def baseEnd_483509 : Nat := 220686682466536891123457

theorem tailTrace_483509 : CollatzResearch.WordTrace tailWord_483509 prefixEnd_483509 220686682466536891123457 := by
  unfold tailWord_483509
  simp only [CollatzResearch.WordTrace]
  refine ⟨17635022005336944608037581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11756681336891296405358387 17635022005336944608037581)
  ·
    refine ⟨6613133252001354228014093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17635022005336944608037581 6613133252001354228014093)
    ·
      refine ⟨2479924969500507835505285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6613133252001354228014093 2479924969500507835505285)
      ·
        refine ⟨464985931781345219157241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2479924969500507835505285 464985931781345219157241)
        ·
          refine ⟨348739448836008914367931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464985931781345219157241 348739448836008914367931)
          ·
            refine ⟨523109173254013371551897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348739448836008914367931 523109173254013371551897)
            ·
              refine ⟨392331879940510028663923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523109173254013371551897 392331879940510028663923)
              ·
                refine ⟨588497819910765042995885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392331879940510028663923 588497819910765042995885)
                ·
                  refine ⟨220686682466536891123457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 588497819910765042995885 220686682466536891123457)
                  ·
                    rfl

theorem cell20_483509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_483509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483509 prefixEnd_483509 := by exact prefixLift 483509
  have htrace : WordTrace (prefixWord ++ tailWord_483509) baseStart_483509 baseEnd_483509 := by
    simpa [prefixWord, tailWord_483509, baseEnd_483509] using wordTrace_append hprefix tailTrace_483509
  have hstable : (prefixWord ++ tailWord_483509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483509).length < 2 ^ (prefixWord ++ tailWord_483509).sum := by decide
  have hdescent : baseEnd_483509 < baseStart_483509 := by decide
  rcases family_descends (prefixWord ++ tailWord_483509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483548 : List Nat := [2, 2, 5, 2, 9]
def baseStart_483548 : Nat := 118140960795 + 483548 * 2 ^ 59
def prefixEnd_483548 : Nat := 4983230072969 + 3 ^ 40 * 483548 * 2
def baseEnd_483548 : Nat := 2724746705299087516337

theorem tailTrace_483548 : CollatzResearch.WordTrace tailWord_483548 prefixEnd_483548 2724746705299087516337 := by
  unfold tailWord_483548
  simp only [CollatzResearch.WordTrace]
  refine ⟨8818222226097827134353649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11757629634797102845804865 8818222226097827134353649)
  ·
    refine ⟨6613666669573370350765237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8818222226097827134353649 6613666669573370350765237)
    ·
      refine ⟨620031250272503470384241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6613666669573370350765237 620031250272503470384241)
      ·
        refine ⟨465023437704377602788181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620031250272503470384241 465023437704377602788181)
        ·
          refine ⟨2724746705299087516337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 465023437704377602788181 2724746705299087516337)
          ·
            rfl

theorem cell20_483548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 9].length) (baseStart_483548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483548 prefixEnd_483548 := by exact prefixLift 483548
  have htrace : WordTrace (prefixWord ++ tailWord_483548) baseStart_483548 baseEnd_483548 := by
    simpa [prefixWord, tailWord_483548, baseEnd_483548] using wordTrace_append hprefix tailTrace_483548
  have hstable : (prefixWord ++ tailWord_483548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483548).length < 2 ^ (prefixWord ++ tailWord_483548).sum := by decide
  have hdescent : baseEnd_483548 < baseStart_483548 := by decide
  rcases family_descends (prefixWord ++ tailWord_483548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483562 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_483562 : Nat := 118140960795 + 483562 * 2 ^ 59
def prefixEnd_483562 : Nat := 4983230072969 + 3 ^ 40 * 483562 * 2
def baseEnd_483562 : Nat := 220710873110704262356573

theorem tailTrace_483562 : CollatzResearch.WordTrace tailWord_483562 prefixEnd_483562 220710873110704262356573 := by
  unfold tailWord_483562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4409238768536233664929235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11757970049429956439811293 4409238768536233664929235)
  ·
    refine ⟨6613858152804350497393853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4409238768536233664929235 6613858152804350497393853)
    ·
      refine ⟨2480196807301631436522695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6613858152804350497393853 2480196807301631436522695)
      ·
        refine ⟨3720295210952447154784043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480196807301631436522695 3720295210952447154784043)
        ·
          refine ⟨5580442816428670732176065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3720295210952447154784043 5580442816428670732176065)
          ·
            refine ⟨4185332112321503049132049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5580442816428670732176065 4185332112321503049132049)
            ·
              refine ⟨3138999084241127286849037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4185332112321503049132049 3138999084241127286849037)
              ·
                refine ⟨1177124656590422732568389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3138999084241127286849037 1177124656590422732568389)
                ·
                  refine ⟨220710873110704262356573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1177124656590422732568389 220710873110704262356573)
                  ·
                    rfl

theorem cell20_483562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_483562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483562 prefixEnd_483562 := by exact prefixLift 483562
  have htrace : WordTrace (prefixWord ++ tailWord_483562) baseStart_483562 baseEnd_483562 := by
    simpa [prefixWord, tailWord_483562, baseEnd_483562] using wordTrace_append hprefix tailTrace_483562
  have hstable : (prefixWord ++ tailWord_483562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483562).length < 2 ^ (prefixWord ++ tailWord_483562).sum := by decide
  have hdescent : baseEnd_483562 < baseStart_483562 := by decide
  rcases family_descends (prefixWord ++ tailWord_483562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483565 : List Nat := [1, 5, 1, 2, 3, 2, 1, 5]
def baseStart_483565 : Nat := 118140960795 + 483565 * 2 ^ 59
def prefixEnd_483565 : Nat := 4983230072969 + 3 ^ 40 * 483565 * 2
def baseEnd_483565 : Nat := 73570747464149861752187

theorem tailTrace_483565 : CollatzResearch.WordTrace tailWord_483565 prefixEnd_483565 73570747464149861752187 := by
  unfold tailWord_483565
  simp only [CollatzResearch.WordTrace]
  refine ⟨17637064493134066172076149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11758042995422710781384099 17637064493134066172076149)
  ·
    refine ⟨1653474796231318703632139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17637064493134066172076149 1653474796231318703632139)
    ·
      refine ⟨2480212194346978055448209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1653474796231318703632139 2480212194346978055448209)
      ·
        refine ⟨1860159145760233541586157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2480212194346978055448209 1860159145760233541586157)
        ·
          refine ⟨697559679660087578094809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1860159145760233541586157 697559679660087578094809)
          ·
            refine ⟨523169759745065683571107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 697559679660087578094809 523169759745065683571107)
            ·
              refine ⟨784754639617598525356661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523169759745065683571107 784754639617598525356661)
              ·
                refine ⟨73570747464149861752187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 784754639617598525356661 73570747464149861752187)
                ·
                  rfl

theorem cell20_483565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 5].length) (baseStart_483565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483565 prefixEnd_483565 := by exact prefixLift 483565
  have htrace : WordTrace (prefixWord ++ tailWord_483565) baseStart_483565 baseEnd_483565 := by
    simpa [prefixWord, tailWord_483565, baseEnd_483565] using wordTrace_append hprefix tailTrace_483565
  have hstable : (prefixWord ++ tailWord_483565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483565).length < 2 ^ (prefixWord ++ tailWord_483565).sum := by decide
  have hdescent : baseEnd_483565 < baseStart_483565 := by decide
  rcases family_descends (prefixWord ++ tailWord_483565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483569 : List Nat := [1, 2, 2, 2, 2, 1, 5, 5]
def baseStart_483569 : Nat := 118140960795 + 483569 * 2 ^ 59
def prefixEnd_483569 : Nat := 4983230072969 + 3 ^ 40 * 483569 * 2
def baseEnd_483569 : Nat := 73571356033814449707737

theorem tailTrace_483569 : CollatzResearch.WordTrace tailWord_483569 prefixEnd_483569 73571356033814449707737 := by
  unfold tailWord_483569
  simp only [CollatzResearch.WordTrace]
  refine ⟨17637210385119574855221761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11758140256746383236814507 17637210385119574855221761)
  ·
    refine ⟨13227907788839681141416321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17637210385119574855221761 13227907788839681141416321)
    ·
      refine ⟨9920930841629760856062241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13227907788839681141416321 9920930841629760856062241)
      ·
        refine ⟨7440698131222320642046681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9920930841629760856062241 7440698131222320642046681)
        ·
          refine ⟨5580523598416740481535011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7440698131222320642046681 5580523598416740481535011)
          ·
            refine ⟨8370785397625110722302517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5580523598416740481535011 8370785397625110722302517)
            ·
              refine ⟨784761131027354130215861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8370785397625110722302517 784761131027354130215861)
              ·
                refine ⟨73571356033814449707737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 784761131027354130215861 73571356033814449707737)
                ·
                  rfl

theorem cell20_483569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 5].length) (baseStart_483569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483569 prefixEnd_483569 := by exact prefixLift 483569
  have htrace : WordTrace (prefixWord ++ tailWord_483569) baseStart_483569 baseEnd_483569 := by
    simpa [prefixWord, tailWord_483569, baseEnd_483569] using wordTrace_append hprefix tailTrace_483569
  have hstable : (prefixWord ++ tailWord_483569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483569).length < 2 ^ (prefixWord ++ tailWord_483569).sum := by decide
  have hdescent : baseEnd_483569 < baseStart_483569 := by decide
  rcases family_descends (prefixWord ++ tailWord_483569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483607 : List Nat := [1, 1, 3, 4, 1, 3, 7]
def baseStart_483607 : Nat := 118140960795 + 483607 * 2 ^ 59
def prefixEnd_483607 : Nat := 4983230072969 + 3 ^ 40 * 483607 * 2
def baseEnd_483607 : Nat := 24525712481876011761821

theorem tailTrace_483607 : CollatzResearch.WordTrace tailWord_483607 prefixEnd_483607 24525712481876011761821 := by
  unfold tailWord_483607
  simp only [CollatzResearch.WordTrace]
  refine ⟨17638596358981907345105075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11759064239321271563403383 17638596358981907345105075)
  ·
    refine ⟨26457894538472861017657613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17638596358981907345105075 26457894538472861017657613)
    ·
      refine ⟨9921710451927322881621605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26457894538472861017657613 9921710451927322881621605)
      ·
        refine ⟨1860320709736373040304051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9921710451927322881621605 1860320709736373040304051)
        ·
          refine ⟨2790481064604559560456077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1860320709736373040304051 2790481064604559560456077)
          ·
            refine ⟨1046430399226709835171029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2790481064604559560456077 1046430399226709835171029)
            ·
              refine ⟨24525712481876011761821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1046430399226709835171029 24525712481876011761821)
              ·
                rfl

theorem cell20_483607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 7].length) (baseStart_483607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483607 prefixEnd_483607 := by exact prefixLift 483607
  have htrace : WordTrace (prefixWord ++ tailWord_483607) baseStart_483607 baseEnd_483607 := by
    simpa [prefixWord, tailWord_483607, baseEnd_483607] using wordTrace_append hprefix tailTrace_483607
  have hstable : (prefixWord ++ tailWord_483607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483607).length < 2 ^ (prefixWord ++ tailWord_483607).sum := by decide
  have hdescent : baseEnd_483607 < baseStart_483607 := by decide
  rcases family_descends (prefixWord ++ tailWord_483607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483617 : List Nat := [1, 2, 3, 2, 1, 1, 4, 4, 2]
def baseStart_483617 : Nat := 118140960795 + 483617 * 2 ^ 59
def prefixEnd_483617 : Nat := 4983230072969 + 3 ^ 40 * 483617 * 2
def baseEnd_483617 : Nat := 220735976609368515523015

theorem tailTrace_483617 : CollatzResearch.WordTrace tailWord_483617 prefixEnd_483617 220735976609368515523015 := by
  unfold tailWord_483617
  simp only [CollatzResearch.WordTrace]
  refine ⟨17638961088945679052969105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11759307392630452701979403 17638961088945679052969105)
  ·
    refine ⟨13229220816709259289726829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17638961088945679052969105 13229220816709259289726829)
    ·
      refine ⟨4960957806265972233647561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13229220816709259289726829 4960957806265972233647561)
      ·
        refine ⟨3720718354699479175235671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4960957806265972233647561 3720718354699479175235671)
        ·
          refine ⟨5581077532049218762853507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3720718354699479175235671 5581077532049218762853507)
          ·
            refine ⟨8371616298073828144280261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5581077532049218762853507 8371616298073828144280261)
            ·
              refine ⟨1569678055888842777052549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8371616298073828144280261 1569678055888842777052549)
              ·
                refine ⟨294314635479158020697353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1569678055888842777052549 294314635479158020697353)
                ·
                  refine ⟨220735976609368515523015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294314635479158020697353 220735976609368515523015)
                  ·
                    rfl

theorem cell20_483617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 2].length) (baseStart_483617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483617 prefixEnd_483617 := by exact prefixLift 483617
  have htrace : WordTrace (prefixWord ++ tailWord_483617) baseStart_483617 baseEnd_483617 := by
    simpa [prefixWord, tailWord_483617, baseEnd_483617] using wordTrace_append hprefix tailTrace_483617
  have hstable : (prefixWord ++ tailWord_483617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483617).length < 2 ^ (prefixWord ++ tailWord_483617).sum := by decide
  have hdescent : baseEnd_483617 < baseStart_483617 := by decide
  rcases family_descends (prefixWord ++ tailWord_483617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483623 : List Nat := [1, 1, 8, 1, 1, 1, 3, 1, 3]
def baseStart_483623 : Nat := 118140960795 + 483623 * 2 ^ 59
def prefixEnd_483623 : Nat := 4983230072969 + 3 ^ 40 * 483623 * 2
def baseEnd_483623 : Nat := 220738715172859161322991

theorem tailTrace_483623 : CollatzResearch.WordTrace tailWord_483623 prefixEnd_483623 220738715172859161322991 := by
  unfold tailWord_483623
  simp only [CollatzResearch.WordTrace]
  refine ⟨17639179926923942077687523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11759453284615961385125015 17639179926923942077687523)
  ·
    refine ⟨26458769890385913116531285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17639179926923942077687523 26458769890385913116531285)
    ·
      refine ⟨310063709652959919334351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 26458769890385913116531285 310063709652959919334351)
      ·
        refine ⟨465095564479439879001527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310063709652959919334351 465095564479439879001527)
        ·
          refine ⟨697643346719159818502291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465095564479439879001527 697643346719159818502291)
          ·
            refine ⟨1046465020078739727753437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697643346719159818502291 1046465020078739727753437)
            ·
              refine ⟨392424382529527397907539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1046465020078739727753437 392424382529527397907539)
              ·
                refine ⟨588636573794291096861309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392424382529527397907539 588636573794291096861309)
                ·
                  refine ⟨220738715172859161322991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 588636573794291096861309 220738715172859161322991)
                  ·
                    rfl

theorem cell20_483623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 3].length) (baseStart_483623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483623 prefixEnd_483623 := by exact prefixLift 483623
  have htrace : WordTrace (prefixWord ++ tailWord_483623) baseStart_483623 baseEnd_483623 := by
    simpa [prefixWord, tailWord_483623, baseEnd_483623] using wordTrace_append hprefix tailTrace_483623
  have hstable : (prefixWord ++ tailWord_483623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483623).length < 2 ^ (prefixWord ++ tailWord_483623).sum := by decide
  have hdescent : baseEnd_483623 < baseStart_483623 := by decide
  rcases family_descends (prefixWord ++ tailWord_483623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483641 : List Nat := [1, 2, 1, 6, 1, 3, 2, 4]
def baseStart_483641 : Nat := 118140960795 + 483641 * 2 ^ 59
def prefixEnd_483641 : Nat := 4983230072969 + 3 ^ 40 * 483641 * 2
def baseEnd_483641 : Nat := 73582310287777032907639

theorem tailTrace_483641 : CollatzResearch.WordTrace tailWord_483641 prefixEnd_483641 73582310287777032907639 := by
  unfold tailWord_483641
  simp only [CollatzResearch.WordTrace]
  refine ⟨17639836440858731151842777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11759890960572487434561851 17639836440858731151842777)
  ·
    refine ⟨13229877330644048363882083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17639836440858731151842777 13229877330644048363882083)
    ·
      refine ⟨19844815995966072545823125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13229877330644048363882083 19844815995966072545823125)
      ·
        refine ⟨930225749810909650585459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19844815995966072545823125 930225749810909650585459)
        ·
          refine ⟨1395338624716364475878189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930225749810909650585459 1395338624716364475878189)
          ·
            refine ⟨523251984268636678454321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1395338624716364475878189 523251984268636678454321)
            ·
              refine ⟨392438988201477508840741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523251984268636678454321 392438988201477508840741)
              ·
                refine ⟨73582310287777032907639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 392438988201477508840741 73582310287777032907639)
                ·
                  rfl

theorem cell20_483641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 4].length) (baseStart_483641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483641 prefixEnd_483641 := by exact prefixLift 483641
  have htrace : WordTrace (prefixWord ++ tailWord_483641) baseStart_483641 baseEnd_483641 := by
    simpa [prefixWord, tailWord_483641, baseEnd_483641] using wordTrace_append hprefix tailTrace_483641
  have hstable : (prefixWord ++ tailWord_483641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483641).length < 2 ^ (prefixWord ++ tailWord_483641).sum := by decide
  have hdescent : baseEnd_483641 < baseStart_483641 := by decide
  rcases family_descends (prefixWord ++ tailWord_483641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483683 : List Nat := [1, 1, 1, 5, 2, 1, 4, 5]
def baseStart_483683 : Nat := 118140960795 + 483683 * 2 ^ 59
def prefixEnd_483683 : Nat := 4983230072969 + 3 ^ 40 * 483683 * 2
def baseEnd_483683 : Nat := 73588700269255206440915

theorem tailTrace_483683 : CollatzResearch.WordTrace tailWord_483683 prefixEnd_483683 73588700269255206440915 := by
  unfold tailWord_483683
  simp only [CollatzResearch.WordTrace]
  refine ⟨17641368306706572324871703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11760912204471048216581135 17641368306706572324871703)
  ·
    refine ⟨26462052460059858487307555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17641368306706572324871703 26462052460059858487307555)
    ·
      refine ⟨39693078690089787730961333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26462052460059858487307555 39693078690089787730961333)
      ·
        refine ⟨3721226127195917599777625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39693078690089787730961333 3721226127195917599777625)
        ·
          refine ⟨2790919595396938199833219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3721226127195917599777625 2790919595396938199833219)
          ·
            refine ⟨4186379393095407299749829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2790919595396938199833219 4186379393095407299749829)
            ·
              refine ⟨784946136205388868703093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4186379393095407299749829 784946136205388868703093)
              ·
                refine ⟨73588700269255206440915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 784946136205388868703093 73588700269255206440915)
                ·
                  rfl

theorem cell20_483683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 5].length) (baseStart_483683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483683 prefixEnd_483683 := by exact prefixLift 483683
  have htrace : WordTrace (prefixWord ++ tailWord_483683) baseStart_483683 baseEnd_483683 := by
    simpa [prefixWord, tailWord_483683, baseEnd_483683] using wordTrace_append hprefix tailTrace_483683
  have hstable : (prefixWord ++ tailWord_483683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483683).length < 2 ^ (prefixWord ++ tailWord_483683).sum := by decide
  have hdescent : baseEnd_483683 < baseStart_483683 := by decide
  rcases family_descends (prefixWord ++ tailWord_483683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483697 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 6]
def baseStart_483697 : Nat := 118140960795 + 483697 * 2 ^ 59
def prefixEnd_483697 : Nat := 4983230072969 + 3 ^ 40 * 483697 * 2
def baseEnd_483697 : Nat := 220772490789243792856021

theorem tailTrace_483697 : CollatzResearch.WordTrace tailWord_483697 prefixEnd_483697 220772490789243792856021 := by
  unfold tailWord_483697
  simp only [CollatzResearch.WordTrace]
  refine ⟨17641878928655852715881345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11761252619103901810587563 17641878928655852715881345)
  ·
    refine ⟨13231409196491889536911009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17641878928655852715881345 13231409196491889536911009)
    ·
      refine ⟨9923556897368917152683257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13231409196491889536911009 9923556897368917152683257)
      ·
        refine ⟨7442667673026687864512443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9923556897368917152683257 7442667673026687864512443)
        ·
          refine ⟨11164001509540031796768665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7442667673026687864512443 11164001509540031796768665)
          ·
            refine ⟨8373001132155023847576499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11164001509540031796768665 8373001132155023847576499)
            ·
              refine ⟨12559501698232535771364749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8373001132155023847576499 12559501698232535771364749)
              ·
                refine ⟨4709813136837200914261781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12559501698232535771364749 4709813136837200914261781)
                ·
                  refine ⟨220772490789243792856021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4709813136837200914261781 220772490789243792856021)
                  ·
                    rfl

theorem cell20_483697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_483697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483697 prefixEnd_483697 := by exact prefixLift 483697
  have htrace : WordTrace (prefixWord ++ tailWord_483697) baseStart_483697 baseEnd_483697 := by
    simpa [prefixWord, tailWord_483697, baseEnd_483697] using wordTrace_append hprefix tailTrace_483697
  have hstable : (prefixWord ++ tailWord_483697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483697).length < 2 ^ (prefixWord ++ tailWord_483697).sum := by decide
  have hdescent : baseEnd_483697 < baseStart_483697 := by decide
  rcases family_descends (prefixWord ++ tailWord_483697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483738 : List Nat := [3, 1, 1, 4, 1, 4, 1, 5]
def baseStart_483738 : Nat := 118140960795 + 483738 * 2 ^ 59
def prefixEnd_483738 : Nat := 4983230072969 + 3 ^ 40 * 483738 * 2
def baseEnd_483738 : Nat := 73597068102143290829729

theorem tailTrace_483738 : CollatzResearch.WordTrace tailWord_483738 prefixEnd_483738 73597068102143290829729 := by
  unfold tailWord_483738
  simp only [CollatzResearch.WordTrace]
  refine ⟨4410843580376829179530967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11762249547671544478749245 4410843580376829179530967)
  ·
    refine ⟨6616265370565243769296451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4410843580376829179530967 6616265370565243769296451)
    ·
      refine ⟨9924398055847865653944677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6616265370565243769296451 9924398055847865653944677)
      ·
        refine ⟨1860824635471474810114627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9924398055847865653944677 1860824635471474810114627)
        ·
          refine ⟨2791236953207212215171941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1860824635471474810114627 2791236953207212215171941)
          ·
            refine ⟨523356928726352290344739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2791236953207212215171941 523356928726352290344739)
            ·
              refine ⟨785035393089528435517109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523356928726352290344739 785035393089528435517109)
              ·
                refine ⟨73597068102143290829729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 785035393089528435517109 73597068102143290829729)
                ·
                  rfl

theorem cell20_483738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_483738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483738 prefixEnd_483738 := by exact prefixLift 483738
  have htrace : WordTrace (prefixWord ++ tailWord_483738) baseStart_483738 baseEnd_483738 := by
    simpa [prefixWord, tailWord_483738, baseEnd_483738] using wordTrace_append hprefix tailTrace_483738
  have hstable : (prefixWord ++ tailWord_483738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483738).length < 2 ^ (prefixWord ++ tailWord_483738).sum := by decide
  have hdescent : baseEnd_483738 < baseStart_483738 := by decide
  rcases family_descends (prefixWord ++ tailWord_483738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483769 : List Nat := [1, 2, 1, 4, 3, 1, 1, 5, 2]
def baseStart_483769 : Nat := 118140960795 + 483769 * 2 ^ 59
def prefixEnd_483769 : Nat := 4983230072969 + 3 ^ 40 * 483769 * 2
def baseEnd_483769 : Nat := 220805353551131542455727

theorem tailTrace_483769 : CollatzResearch.WordTrace tailWord_483769 prefixEnd_483769 220805353551131542455727 := by
  unfold tailWord_483769
  simp only [CollatzResearch.WordTrace]
  refine ⟨17644504984395009012502361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11763003322930006008334907 17644504984395009012502361)
  ·
    refine ⟨13233378738296256759376771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17644504984395009012502361 13233378738296256759376771)
    ·
      refine ⟨19850068107444385139065157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13233378738296256759376771 19850068107444385139065157)
      ·
        refine ⟨3721887770145822213574717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19850068107444385139065157 3721887770145822213574717)
        ·
          refine ⟨1395707913804683330090519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3721887770145822213574717 1395707913804683330090519)
          ·
            refine ⟨2093561870707024995135779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395707913804683330090519 2093561870707024995135779)
            ·
              refine ⟨3140342806060537492703669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093561870707024995135779 3140342806060537492703669)
              ·
                refine ⟨294407138068175389940969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3140342806060537492703669 294407138068175389940969)
                ·
                  refine ⟨220805353551131542455727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294407138068175389940969 220805353551131542455727)
                  ·
                    rfl

theorem cell20_483769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 2].length) (baseStart_483769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483769 prefixEnd_483769 := by exact prefixLift 483769
  have htrace : WordTrace (prefixWord ++ tailWord_483769) baseStart_483769 baseEnd_483769 := by
    simpa [prefixWord, tailWord_483769, baseEnd_483769] using wordTrace_append hprefix tailTrace_483769
  have hstable : (prefixWord ++ tailWord_483769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483769).length < 2 ^ (prefixWord ++ tailWord_483769).sum := by decide
  have hdescent : baseEnd_483769 < baseStart_483769 := by decide
  rcases family_descends (prefixWord ++ tailWord_483769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483783 : List Nat := [1, 1, 4, 1, 1, 4, 3, 2, 3]
def baseStart_483783 : Nat := 118140960795 + 483783 * 2 ^ 59
def prefixEnd_483783 : Nat := 4983230072969 + 3 ^ 40 * 483783 * 2
def baseEnd_483783 : Nat := 220811743532609715989003

theorem tailTrace_483783 : CollatzResearch.WordTrace tailWord_483783 prefixEnd_483783 220811743532609715989003 := by
  unfold tailWord_483783
  simp only [CollatzResearch.WordTrace]
  refine ⟨17645015606344289403512003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11763343737562859602341335 17645015606344289403512003)
  ·
    refine ⟨26467523409516434105268005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17645015606344289403512003 26467523409516434105268005)
    ·
      refine ⟨4962660639284331394737751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26467523409516434105268005 4962660639284331394737751)
      ·
        refine ⟨7443990958926497092106627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4962660639284331394737751 7443990958926497092106627)
        ·
          refine ⟨11165986438389745638159941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7443990958926497092106627 11165986438389745638159941)
          ·
            refine ⟨2093622457198077307154989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11165986438389745638159941 2093622457198077307154989)
            ·
              refine ⟨785108421449278990183121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2093622457198077307154989 785108421449278990183121)
              ·
                refine ⟨588831316086959242637341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785108421449278990183121 588831316086959242637341)
                ·
                  refine ⟨220811743532609715989003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 588831316086959242637341 220811743532609715989003)
                  ·
                    rfl

theorem cell20_483783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 3].length) (baseStart_483783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483783 prefixEnd_483783 := by exact prefixLift 483783
  have htrace : WordTrace (prefixWord ++ tailWord_483783) baseStart_483783 baseEnd_483783 := by
    simpa [prefixWord, tailWord_483783, baseEnd_483783] using wordTrace_append hprefix tailTrace_483783
  have hstable : (prefixWord ++ tailWord_483783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483783).length < 2 ^ (prefixWord ++ tailWord_483783).sum := by decide
  have hdescent : baseEnd_483783 < baseStart_483783 := by decide
  rcases family_descends (prefixWord ++ tailWord_483783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483821 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 5]
def baseStart_483821 : Nat := 118140960795 + 483821 * 2 ^ 59
def prefixEnd_483821 : Nat := 4983230072969 + 3 ^ 40 * 483821 * 2
def baseEnd_483821 : Nat := 220829087768050472722181

theorem tailTrace_483821 : CollatzResearch.WordTrace tailWord_483821 prefixEnd_483821 220829087768050472722181 := by
  unfold tailWord_483821
  simp only [CollatzResearch.WordTrace]
  refine ⟨17646401580206621893395317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11764267720137747928930211 17646401580206621893395317)
  ·
    refine ⟨1654350148144370802505811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17646401580206621893395317 1654350148144370802505811)
    ·
      refine ⟨2481525222216556203758717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1654350148144370802505811 2481525222216556203758717)
      ·
        refine ⟨930571958331208576409519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2481525222216556203758717 930571958331208576409519)
        ·
          refine ⟨1395857937496812864614279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930571958331208576409519 1395857937496812864614279)
          ·
            refine ⟨2093786906245219296921419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395857937496812864614279 2093786906245219296921419)
            ·
              refine ⟨3140680359367828945382129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093786906245219296921419 3140680359367828945382129)
              ·
                refine ⟨2355510269525871709036597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3140680359367828945382129 2355510269525871709036597)
                ·
                  refine ⟨220829087768050472722181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2355510269525871709036597 220829087768050472722181)
                  ·
                    rfl

theorem cell20_483821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_483821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483821 prefixEnd_483821 := by exact prefixLift 483821
  have htrace : WordTrace (prefixWord ++ tailWord_483821) baseStart_483821 baseEnd_483821 := by
    simpa [prefixWord, tailWord_483821, baseEnd_483821] using wordTrace_append hprefix tailTrace_483821
  have hstable : (prefixWord ++ tailWord_483821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483821).length < 2 ^ (prefixWord ++ tailWord_483821).sum := by decide
  have hdescent : baseEnd_483821 < baseStart_483821 := by decide
  rcases family_descends (prefixWord ++ tailWord_483821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483849 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 4]
def baseStart_483849 : Nat := 118140960795 + 483849 * 2 ^ 59
def prefixEnd_483849 : Nat := 4983230072969 + 3 ^ 40 * 483849 * 2
def baseEnd_483849 : Nat := 220841867731006819788733

theorem tailTrace_483849 : CollatzResearch.WordTrace tailWord_483849 prefixEnd_483849 220841867731006819788733 := by
  unfold tailWord_483849
  simp only [CollatzResearch.WordTrace]
  refine ⟨17647422824105182675414601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11764948549403455116943067 17647422824105182675414601)
  ·
    refine ⟨13235567118078887006560951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17647422824105182675414601 13235567118078887006560951)
    ·
      refine ⟨19853350677118330509841427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13235567118078887006560951 19853350677118330509841427)
      ·
        refine ⟨29780026015677495764762141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19853350677118330509841427 29780026015677495764762141)
        ·
          refine ⟨11167509755879060911785803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29780026015677495764762141 11167509755879060911785803)
          ·
            refine ⟨16751264633818591367678705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11167509755879060911785803 16751264633818591367678705)
            ·
              refine ⟨12563448475363943525759029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16751264633818591367678705 12563448475363943525759029)
              ·
                refine ⟨1177823294565369705539909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12563448475363943525759029 1177823294565369705539909)
                ·
                  refine ⟨220841867731006819788733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1177823294565369705539909 220841867731006819788733)
                  ·
                    rfl

theorem cell20_483849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_483849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483849 prefixEnd_483849 := by exact prefixLift 483849
  have htrace : WordTrace (prefixWord ++ tailWord_483849) baseStart_483849 baseEnd_483849 := by
    simpa [prefixWord, tailWord_483849, baseEnd_483849] using wordTrace_append hprefix tailTrace_483849
  have hstable : (prefixWord ++ tailWord_483849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483849).length < 2 ^ (prefixWord ++ tailWord_483849).sum := by decide
  have hdescent : baseEnd_483849 < baseStart_483849 := by decide
  rcases family_descends (prefixWord ++ tailWord_483849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483897 : List Nat := [1, 2, 1, 5, 1, 1, 4, 2, 3]
def baseStart_483897 : Nat := 118140960795 + 483897 * 2 ^ 59
def prefixEnd_483897 : Nat := 4983230072969 + 3 ^ 40 * 483897 * 2
def baseEnd_483897 : Nat := 220863776238931986188537

theorem tailTrace_483897 : CollatzResearch.WordTrace tailWord_483897 prefixEnd_483897 220863776238931986188537 := by
  unfold tailWord_483897
  simp only [CollatzResearch.WordTrace]
  refine ⟨17649173527931286873161945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11766115685287524582107963 17649173527931286873161945)
  ·
    refine ⟨13236880145948465154871459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17649173527931286873161945 13236880145948465154871459)
    ·
      refine ⟨19855320218922697732307189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13236880145948465154871459 19855320218922697732307189)
      ·
        refine ⟨1861436270524002912403799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19855320218922697732307189 1861436270524002912403799)
        ·
          refine ⟨2792154405786004368605699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861436270524002912403799 2792154405786004368605699)
          ·
            refine ⟨4188231608679006552908549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792154405786004368605699 4188231608679006552908549)
            ·
              refine ⟨785293426627313728670353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4188231608679006552908549 785293426627313728670353)
              ·
                refine ⟨588970069970485296502765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785293426627313728670353 588970069970485296502765)
                ·
                  refine ⟨220863776238931986188537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 588970069970485296502765 220863776238931986188537)
                  ·
                    rfl

theorem cell20_483897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_483897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483897 prefixEnd_483897 := by exact prefixLift 483897
  have htrace : WordTrace (prefixWord ++ tailWord_483897) baseStart_483897 baseEnd_483897 := by
    simpa [prefixWord, tailWord_483897, baseEnd_483897] using wordTrace_append hprefix tailTrace_483897
  have hstable : (prefixWord ++ tailWord_483897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483897).length < 2 ^ (prefixWord ++ tailWord_483897).sum := by decide
  have hdescent : baseEnd_483897 < baseStart_483897 := by decide
  rcases family_descends (prefixWord ++ tailWord_483897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483900 : List Nat := [2, 2, 2, 2, 3, 1, 4, 2, 2]
def baseStart_483900 : Nat := 118140960795 + 483900 * 2 ^ 59
def prefixEnd_483900 : Nat := 4983230072969 + 3 ^ 40 * 483900 * 2
def baseEnd_483900 : Nat := 220865145520677309088525

theorem tailTrace_483900 : CollatzResearch.WordTrace tailWord_483900 prefixEnd_483900 220865145520677309088525 := by
  unfold tailWord_483900
  simp only [CollatzResearch.WordTrace]
  refine ⟨8824641473460209192760577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11766188631280278923680769 8824641473460209192760577)
  ·
    refine ⟨6618481105095156894570433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8824641473460209192760577 6618481105095156894570433)
    ·
      refine ⟨4963860828821367670927825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6618481105095156894570433 4963860828821367670927825)
      ·
        refine ⟨3722895621616025753195869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4963860828821367670927825 3722895621616025753195869)
        ·
          refine ⟨1396085858106009657448451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3722895621616025753195869 1396085858106009657448451)
          ·
            refine ⟨2094128787159014486172677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396085858106009657448451 2094128787159014486172677)
            ·
              refine ⟨392649147592315216157377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2094128787159014486172677 392649147592315216157377)
              ·
                refine ⟨294486860694236412118033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392649147592315216157377 294486860694236412118033)
                ·
                  refine ⟨220865145520677309088525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294486860694236412118033 220865145520677309088525)
                  ·
                    rfl

theorem cell20_483900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_483900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483900 prefixEnd_483900 := by exact prefixLift 483900
  have htrace : WordTrace (prefixWord ++ tailWord_483900) baseStart_483900 baseEnd_483900 := by
    simpa [prefixWord, tailWord_483900, baseEnd_483900] using wordTrace_append hprefix tailTrace_483900
  have hstable : (prefixWord ++ tailWord_483900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483900).length < 2 ^ (prefixWord ++ tailWord_483900).sum := by decide
  have hdescent : baseEnd_483900 < baseStart_483900 := by decide
  rcases family_descends (prefixWord ++ tailWord_483900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483911 : List Nat := [1, 1, 4, 1, 4, 1, 3, 5]
def baseStart_483911 : Nat := 118140960795 + 483911 * 2 ^ 59
def prefixEnd_483911 : Nat := 4983230072969 + 3 ^ 40 * 483911 * 2
def baseEnd_483911 : Nat := 73623388740136719907271

theorem tailTrace_483911 : CollatzResearch.WordTrace tailWord_483911 prefixEnd_483911 73623388740136719907271 := by
  unfold tailWord_483911
  simp only [CollatzResearch.WordTrace]
  refine ⟨17649684149880567264171587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11766456099920378176114391 17649684149880567264171587)
  ·
    refine ⟨26474526224820850896257381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17649684149880567264171587 26474526224820850896257381)
    ·
      refine ⟨4963973667153909543048259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26474526224820850896257381 4963973667153909543048259)
      ·
        refine ⟨7445960500730864314572389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4963973667153909543048259 7445960500730864314572389)
        ·
          refine ⟨1396117593887037058982323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7445960500730864314572389 1396117593887037058982323)
          ·
            refine ⟨2094176390830555588473485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396117593887037058982323 2094176390830555588473485)
            ·
              refine ⟨785316146561458345677557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2094176390830555588473485 785316146561458345677557)
              ·
                refine ⟨73623388740136719907271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 785316146561458345677557 73623388740136719907271)
                ·
                  rfl

theorem cell20_483911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 5].length) (baseStart_483911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483911 prefixEnd_483911 := by exact prefixLift 483911
  have htrace : WordTrace (prefixWord ++ tailWord_483911) baseStart_483911 baseEnd_483911 := by
    simpa [prefixWord, tailWord_483911, baseEnd_483911] using wordTrace_append hprefix tailTrace_483911
  have hstable : (prefixWord ++ tailWord_483911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483911).length < 2 ^ (prefixWord ++ tailWord_483911).sum := by decide
  have hdescent : baseEnd_483911 < baseStart_483911 := by decide
  rcases family_descends (prefixWord ++ tailWord_483911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483925 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 6]
def baseStart_483925 : Nat := 118140960795 + 483925 * 2 ^ 59
def prefixEnd_483925 : Nat := 4983230072969 + 3 ^ 40 * 483925 * 2
def baseEnd_483925 : Nat := 220876556201888333255089

theorem tailTrace_483925 : CollatzResearch.WordTrace tailWord_483925 prefixEnd_483925 220876556201888333255089 := by
  unfold tailWord_483925
  simp only [CollatzResearch.WordTrace]
  refine ⟨17650194771829847655181229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11766796514553231770120819 17650194771829847655181229)
  ·
    refine ⟨6618823039436192870692961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17650194771829847655181229 6618823039436192870692961)
    ·
      refine ⟨4964117279577144653019721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6618823039436192870692961 4964117279577144653019721)
      ·
        refine ⟨3723087959682858489764791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4964117279577144653019721 3723087959682858489764791)
        ·
          refine ⟨5584631939524287734647187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3723087959682858489764791 5584631939524287734647187)
          ·
            refine ⟨8376947909286431601970781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5584631939524287734647187 8376947909286431601970781)
            ·
              refine ⟨3141355465982411850739043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8376947909286431601970781 3141355465982411850739043)
              ·
                refine ⟨4712033198973617776108565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3141355465982411850739043 4712033198973617776108565)
                ·
                  refine ⟨220876556201888333255089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4712033198973617776108565 220876556201888333255089)
                  ·
                    rfl

theorem cell20_483925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_483925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483925 prefixEnd_483925 := by exact prefixLift 483925
  have htrace : WordTrace (prefixWord ++ tailWord_483925) baseStart_483925 baseEnd_483925 := by
    simpa [prefixWord, tailWord_483925, baseEnd_483925] using wordTrace_append hprefix tailTrace_483925
  have hstable : (prefixWord ++ tailWord_483925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483925).length < 2 ^ (prefixWord ++ tailWord_483925).sum := by decide
  have hdescent : baseEnd_483925 < baseStart_483925 := by decide
  rcases family_descends (prefixWord ++ tailWord_483925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483949 : List Nat := [1, 5, 1, 1, 3, 2, 7]
def baseStart_483949 : Nat := 118140960795 + 483949 * 2 ^ 59
def prefixEnd_483949 : Nat := 4983230072969 + 3 ^ 40 * 483949 * 2
def baseEnd_483949 : Nat := 24543056717316768494999

theorem tailTrace_483949 : CollatzResearch.WordTrace tailWord_483949 prefixEnd_483949 24543056717316768494999 := by
  unfold tailWord_483949
  simp only [CollatzResearch.WordTrace]
  refine ⟨17651070123742899754054901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11767380082495266502703267 17651070123742899754054901)
  ·
    refine ⟨1654787824100896851942647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17651070123742899754054901 1654787824100896851942647)
    ·
      refine ⟨2482181736151345277913971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1654787824100896851942647 2482181736151345277913971)
      ·
        refine ⟨3723272604227017916870957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2482181736151345277913971 3723272604227017916870957)
        ·
          refine ⟨1396227226585131718826609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3723272604227017916870957 1396227226585131718826609)
          ·
            refine ⟨1047170419938848789119957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1396227226585131718826609 1047170419938848789119957)
            ·
              refine ⟨24543056717316768494999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1047170419938848789119957 24543056717316768494999)
              ·
                rfl

theorem cell20_483949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 7].length) (baseStart_483949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483949 prefixEnd_483949 := by exact prefixLift 483949
  have htrace : WordTrace (prefixWord ++ tailWord_483949) baseStart_483949 baseEnd_483949 := by
    simpa [prefixWord, tailWord_483949, baseEnd_483949] using wordTrace_append hprefix tailTrace_483949
  have hstable : (prefixWord ++ tailWord_483949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483949).length < 2 ^ (prefixWord ++ tailWord_483949).sum := by decide
  have hdescent : baseEnd_483949 < baseStart_483949 := by decide
  rcases family_descends (prefixWord ++ tailWord_483949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483952 : List Nat := [2, 1, 1, 1, 7, 2, 1, 2, 3]
def baseStart_483952 : Nat := 118140960795 + 483952 * 2 ^ 59
def prefixEnd_483952 : Nat := 4983230072969 + 3 ^ 40 * 483952 * 2
def baseEnd_483952 : Nat := 220888879737596239354979

theorem tailTrace_483952 : CollatzResearch.WordTrace tailWord_483952 prefixEnd_483952 220888879737596239354979 := by
  unfold tailWord_483952
  simp only [CollatzResearch.WordTrace]
  refine ⟨8825589771366015633207055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11767453028488020844276073 8825589771366015633207055)
  ·
    refine ⟨13238384657049023449810583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8825589771366015633207055 13238384657049023449810583)
    ·
      refine ⟨19857576985573535174715875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13238384657049023449810583 19857576985573535174715875)
      ·
        refine ⟨29786365478360302762073813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19857576985573535174715875 29786365478360302762073813)
        ·
          refine ⟨698117940899069595986105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 29786365478360302762073813 698117940899069595986105)
          ·
            refine ⟨523588455674302196989579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 698117940899069595986105 523588455674302196989579)
            ·
              refine ⟨785382683511453295484369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523588455674302196989579 785382683511453295484369)
              ·
                refine ⟨589037012633589971613277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785382683511453295484369 589037012633589971613277)
                ·
                  refine ⟨220888879737596239354979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 589037012633589971613277 220888879737596239354979)
                  ·
                    rfl

theorem cell20_483952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_483952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483952 prefixEnd_483952 := by exact prefixLift 483952
  have htrace : WordTrace (prefixWord ++ tailWord_483952) baseStart_483952 baseEnd_483952 := by
    simpa [prefixWord, tailWord_483952, baseEnd_483952] using wordTrace_append hprefix tailTrace_483952
  have hstable : (prefixWord ++ tailWord_483952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483952).length < 2 ^ (prefixWord ++ tailWord_483952).sum := by decide
  have hdescent : baseEnd_483952 < baseStart_483952 := by decide
  rcases family_descends (prefixWord ++ tailWord_483952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483997 : List Nat := [1, 4, 2, 1, 1, 1, 5, 3, 2]
def baseStart_483997 : Nat := 118140960795 + 483997 * 2 ^ 59
def prefixEnd_483997 : Nat := 4983230072969 + 3 ^ 40 * 483997 * 2
def baseEnd_483997 : Nat := 220909418963776082854795

theorem tailTrace_483997 : CollatzResearch.WordTrace tailWord_483997 prefixEnd_483997 220909418963776082854795 := by
  unfold tailWord_483997
  simp only [CollatzResearch.WordTrace]
  refine ⟨17652820827569003951802245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11768547218379335967868163 17652820827569003951802245)
  ·
    refine ⟨3309903905169188240962921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17652820827569003951802245 3309903905169188240962921)
    ·
      refine ⟨2482427928876891180722191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3309903905169188240962921 2482427928876891180722191)
      ·
        refine ⟨3723641893315336771083287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2482427928876891180722191 3723641893315336771083287)
        ·
          refine ⟨5585462839973005156624931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3723641893315336771083287 5585462839973005156624931)
          ·
            refine ⟨8378194259959507734937397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5585462839973005156624931 8378194259959507734937397)
            ·
              refine ⟨785455711871203850150381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8378194259959507734937397 785455711871203850150381)
              ·
                refine ⟨294545891951701443806393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 785455711871203850150381 294545891951701443806393)
                ·
                  refine ⟨220909418963776082854795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294545891951701443806393 220909418963776082854795)
                  ·
                    rfl

theorem cell20_483997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_483997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_483997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_483997 prefixEnd_483997 := by exact prefixLift 483997
  have htrace : WordTrace (prefixWord ++ tailWord_483997) baseStart_483997 baseEnd_483997 := by
    simpa [prefixWord, tailWord_483997, baseEnd_483997] using wordTrace_append hprefix tailTrace_483997
  have hstable : (prefixWord ++ tailWord_483997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483997).length < 2 ^ (prefixWord ++ tailWord_483997).sum := by decide
  have hdescent : baseEnd_483997 < baseStart_483997 := by decide
  rcases family_descends (prefixWord ++ tailWord_483997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484010 : List Nat := [3, 1, 5, 2, 1, 1, 3, 2, 2]
def baseStart_484010 : Nat := 118140960795 + 484010 * 2 ^ 59
def prefixEnd_484010 : Nat := 4983230072969 + 3 ^ 40 * 484010 * 2
def baseEnd_484010 : Nat := 220915352518005815421409

theorem tailTrace_484010 : CollatzResearch.WordTrace tailWord_484010 prefixEnd_484010 220915352518005815421409 := by
  unfold tailWord_484010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4413323744130476793006371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11768863317681271448016989 4413323744130476793006371)
  ·
    refine ⟨6619985616195715189509557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4413323744130476793006371 6619985616195715189509557)
    ·
      refine ⟨620623651518348299016521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6619985616195715189509557 620623651518348299016521)
      ·
        refine ⟨465467738638761224262391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620623651518348299016521 465467738638761224262391)
        ·
          refine ⟨698201607958141836393587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465467738638761224262391 698201607958141836393587)
          ·
            refine ⟨1047302411937212754590381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698201607958141836393587 1047302411937212754590381)
            ·
              refine ⟨392738404476454782971393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1047302411937212754590381 392738404476454782971393)
              ·
                refine ⟨294553803357341087228545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392738404476454782971393 294553803357341087228545)
                ·
                  refine ⟨220915352518005815421409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294553803357341087228545 220915352518005815421409)
                  ·
                    rfl

theorem cell20_484010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_484010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484010 prefixEnd_484010 := by exact prefixLift 484010
  have htrace : WordTrace (prefixWord ++ tailWord_484010) baseStart_484010 baseEnd_484010 := by
    simpa [prefixWord, tailWord_484010, baseEnd_484010] using wordTrace_append hprefix tailTrace_484010
  have hstable : (prefixWord ++ tailWord_484010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484010).length < 2 ^ (prefixWord ++ tailWord_484010).sum := by decide
  have hdescent : baseEnd_484010 < baseStart_484010 := by decide
  rcases family_descends (prefixWord ++ tailWord_484010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484014 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_484014 : Nat := 118140960795 + 484014 * 2 ^ 59
def prefixEnd_484014 : Nat := 4983230072969 + 3 ^ 40 * 484014 * 2
def baseEnd_484014 : Nat := 220917178226999579288059

theorem tailTrace_484014 : CollatzResearch.WordTrace tailWord_484014 prefixEnd_484014 220917178226999579288059 := by
  unfold tailWord_484014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2206680108563426981896387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11768960579004943903447397 2206680108563426981896387)
  ·
    refine ⟨3310020162845140472844581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2206680108563426981896387 3310020162845140472844581)
    ·
      refine ⟨620628780533463838658359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3310020162845140472844581 620628780533463838658359)
      ·
        refine ⟨930943170800195757987539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620628780533463838658359 930943170800195757987539)
        ·
          refine ⟨1396414756200293636981309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930943170800195757987539 1396414756200293636981309)
          ·
            refine ⟨523655533575110113867991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1396414756200293636981309 523655533575110113867991)
            ·
              refine ⟨785483300362665170801987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523655533575110113867991 785483300362665170801987)
              ·
                refine ⟨1178224950543997756202981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785483300362665170801987 1178224950543997756202981)
                ·
                  refine ⟨220917178226999579288059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1178224950543997756202981 220917178226999579288059)
                  ·
                    rfl

theorem cell20_484014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_484014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484014 prefixEnd_484014 := by exact prefixLift 484014
  have htrace : WordTrace (prefixWord ++ tailWord_484014) baseStart_484014 baseEnd_484014 := by
    simpa [prefixWord, tailWord_484014, baseEnd_484014] using wordTrace_append hprefix tailTrace_484014
  have hstable : (prefixWord ++ tailWord_484014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484014).length < 2 ^ (prefixWord ++ tailWord_484014).sum := by decide
  have hdescent : baseEnd_484014 < baseStart_484014 := by decide
  rcases family_descends (prefixWord ++ tailWord_484014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484073 : List Nat := [1, 2, 1, 1, 1, 2, 8, 2, 2]
def baseStart_484073 : Nat := 118140960795 + 484073 * 2 ^ 59
def prefixEnd_484073 : Nat := 4983230072969 + 3 ^ 40 * 484073 * 2
def baseEnd_484073 : Nat := 220944107434657596321151

theorem tailTrace_484073 : CollatzResearch.WordTrace tailWord_484073 prefixEnd_484073 220944107434657596321151 := by
  unfold tailWord_484073
  simp only [CollatzResearch.WordTrace]
  refine ⟨17655592775293668931568873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11770395183529112621045915 17655592775293668931568873)
  ·
    refine ⟨13241694581470251698676655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17655592775293668931568873 13241694581470251698676655)
    ·
      refine ⟨19862541872205377548014983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13241694581470251698676655 19862541872205377548014983)
      ·
        refine ⟨29793812808308066322022475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19862541872205377548014983 29793812808308066322022475)
        ·
          refine ⟨44690719212462099483033713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29793812808308066322022475 44690719212462099483033713)
          ·
            refine ⟨33518039409346574612275285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44690719212462099483033713 33518039409346574612275285)
            ·
              refine ⟨392789524328280171237601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 33518039409346574612275285 392789524328280171237601)
              ·
                refine ⟨294592143246210128428201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392789524328280171237601 294592143246210128428201)
                ·
                  refine ⟨220944107434657596321151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294592143246210128428201 220944107434657596321151)
                  ·
                    rfl

theorem cell20_484073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 2].length) (baseStart_484073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484073 prefixEnd_484073 := by exact prefixLift 484073
  have htrace : WordTrace (prefixWord ++ tailWord_484073) baseStart_484073 baseEnd_484073 := by
    simpa [prefixWord, tailWord_484073, baseEnd_484073] using wordTrace_append hprefix tailTrace_484073
  have hstable : (prefixWord ++ tailWord_484073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484073).length < 2 ^ (prefixWord ++ tailWord_484073).sum := by decide
  have hdescent : baseEnd_484073 < baseStart_484073 := by decide
  rcases family_descends (prefixWord ++ tailWord_484073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484094 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_484094 : Nat := 118140960795 + 484094 * 2 ^ 59
def prefixEnd_484094 : Nat := 4983230072969 + 3 ^ 40 * 484094 * 2
def baseEnd_484094 : Nat := 220953692406874856621065

theorem tailTrace_484094 : CollatzResearch.WordTrace tailWord_484094 prefixEnd_484094 220953692406874856621065 := by
  unfold tailWord_484094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2207044838527198689760417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11770905805478393012055557 2207044838527198689760417)
  ·
    refine ⟨1655283628895399017320313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2207044838527198689760417 1655283628895399017320313)
    ·
      refine ⟨1241462721671549262990235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1655283628895399017320313 1241462721671549262990235)
      ·
        refine ⟨1862194082507323894485353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1241462721671549262990235 1862194082507323894485353)
        ·
          refine ⟨1396645561880492920864015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1862194082507323894485353 1396645561880492920864015)
          ·
            refine ⟨2094968342820739381296023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396645561880492920864015 2094968342820739381296023)
            ·
              refine ⟨3142452514231109071944035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2094968342820739381296023 3142452514231109071944035)
              ·
                refine ⟨4713678771346663607916053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3142452514231109071944035 4713678771346663607916053)
                ·
                  refine ⟨220953692406874856621065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4713678771346663607916053 220953692406874856621065)
                  ·
                    rfl

theorem cell20_484094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_484094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484094 prefixEnd_484094 := by exact prefixLift 484094
  have htrace : WordTrace (prefixWord ++ tailWord_484094) baseStart_484094 baseEnd_484094 := by
    simpa [prefixWord, tailWord_484094, baseEnd_484094] using wordTrace_append hprefix tailTrace_484094
  have hstable : (prefixWord ++ tailWord_484094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484094).length < 2 ^ (prefixWord ++ tailWord_484094).sum := by decide
  have hdescent : baseEnd_484094 < baseStart_484094 := by decide
  rcases family_descends (prefixWord ++ tailWord_484094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484122 : List Nat := [3, 1, 1, 3, 2, 1, 9]
def baseStart_484122 : Nat := 118140960795 + 484122 * 2 ^ 59
def prefixEnd_484122 : Nat := 4983230072969 + 3 ^ 40 * 484122 * 2
def baseEnd_484122 : Nat := 24551830263314578187513

theorem tailTrace_484122 : CollatzResearch.WordTrace tailWord_484122 prefixEnd_484122 24551830263314578187513 := by
  unfold tailWord_484122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4414344988029037575025655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11771586634744100200068413 4414344988029037575025655)
  ·
    refine ⟨6621517482043556362538483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4414344988029037575025655 6621517482043556362538483)
    ·
      refine ⟨9932276223065334543807725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6621517482043556362538483 9932276223065334543807725)
      ·
        refine ⟨3724603583649500453927897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9932276223065334543807725 3724603583649500453927897)
        ·
          refine ⟨2793452687737125340445923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3724603583649500453927897 2793452687737125340445923)
          ·
            refine ⟨4190179031605688010668885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2793452687737125340445923 4190179031605688010668885)
            ·
              refine ⟨24551830263314578187513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4190179031605688010668885 24551830263314578187513)
              ·
                rfl

theorem cell20_484122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 9].length) (baseStart_484122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484122 prefixEnd_484122 := by exact prefixLift 484122
  have htrace : WordTrace (prefixWord ++ tailWord_484122) baseStart_484122 baseEnd_484122 := by
    simpa [prefixWord, tailWord_484122, baseEnd_484122] using wordTrace_append hprefix tailTrace_484122
  have hstable : (prefixWord ++ tailWord_484122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484122).length < 2 ^ (prefixWord ++ tailWord_484122).sum := by decide
  have hdescent : baseEnd_484122 < baseStart_484122 := by decide
  rcases family_descends (prefixWord ++ tailWord_484122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484170 : List Nat := [3, 1, 2, 1, 1, 1, 2, 7, 2]
def baseStart_484170 : Nat := 118140960795 + 484170 * 2 ^ 59
def prefixEnd_484170 : Nat := 4983230072969 + 3 ^ 40 * 484170 * 2
def baseEnd_484170 : Nat := 220988380877756370087421

theorem tailTrace_484170 : CollatzResearch.WordTrace tailWord_484170 prefixEnd_484170 220988380877756370087421 := by
  unfold tailWord_484170
  simp only [CollatzResearch.WordTrace]
  refine ⟨4414782663985563624462491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11772753770628169665233309 4414782663985563624462491)
  ·
    refine ⟨6622173995978345436693737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4414782663985563624462491 6622173995978345436693737)
    ·
      refine ⟨4966630496983759077520303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6622173995978345436693737 4966630496983759077520303)
      ·
        refine ⟨7449945745475638616280455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4966630496983759077520303 7449945745475638616280455)
        ·
          refine ⟨11174918618213457924420683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7449945745475638616280455 11174918618213457924420683)
          ·
            refine ⟨16762377927320186886631025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11174918618213457924420683 16762377927320186886631025)
            ·
              refine ⟨12571783445490140164973269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16762377927320186886631025 12571783445490140164973269)
              ·
                refine ⟨294651174503675160116561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12571783445490140164973269 294651174503675160116561)
                ·
                  refine ⟨220988380877756370087421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294651174503675160116561 220988380877756370087421)
                  ·
                    rfl

theorem cell20_484170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_484170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484170 prefixEnd_484170 := by exact prefixLift 484170
  have htrace : WordTrace (prefixWord ++ tailWord_484170) baseStart_484170 baseEnd_484170 := by
    simpa [prefixWord, tailWord_484170, baseEnd_484170] using wordTrace_append hprefix tailTrace_484170
  have hstable : (prefixWord ++ tailWord_484170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484170).length < 2 ^ (prefixWord ++ tailWord_484170).sum := by decide
  have hdescent : baseEnd_484170 < baseStart_484170 := by decide
  rcases family_descends (prefixWord ++ tailWord_484170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484173 : List Nat := [1, 6, 1, 2, 3, 1, 6]
def baseStart_484173 : Nat := 118140960795 + 484173 * 2 ^ 59
def prefixEnd_484173 : Nat := 4983230072969 + 3 ^ 40 * 484173 * 2
def baseEnd_484173 : Nat := 24554416684389076998601

theorem tailTrace_484173 : CollatzResearch.WordTrace tailWord_484173 prefixEnd_484173 24554416684389076998601 := by
  unfold tailWord_484173
  simp only [CollatzResearch.WordTrace]
  refine ⟨17659240074931386010209173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11772826716620924006806115 17659240074931386010209173)
  ·
    refine ⟨827776878512408719228555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17659240074931386010209173 827776878512408719228555)
    ·
      refine ⟨1241665317768613078842833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 827776878512408719228555 1241665317768613078842833)
      ·
        refine ⟨931248988326459809132125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1241665317768613078842833 931248988326459809132125)
        ·
          refine ⟨349218370622422428424547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 931248988326459809132125 349218370622422428424547)
          ·
            refine ⟨523827555933633642636821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349218370622422428424547 523827555933633642636821)
            ·
              refine ⟨24554416684389076998601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 523827555933633642636821 24554416684389076998601)
              ·
                rfl

theorem cell20_484173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 6].length) (baseStart_484173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484173 prefixEnd_484173 := by exact prefixLift 484173
  have htrace : WordTrace (prefixWord ++ tailWord_484173) baseStart_484173 baseEnd_484173 := by
    simpa [prefixWord, tailWord_484173, baseEnd_484173] using wordTrace_append hprefix tailTrace_484173
  have hstable : (prefixWord ++ tailWord_484173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484173).length < 2 ^ (prefixWord ++ tailWord_484173).sum := by decide
  have hdescent : baseEnd_484173 < baseStart_484173 := by decide
  rcases family_descends (prefixWord ++ tailWord_484173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484177 : List Nat := [1, 2, 2, 1, 6, 2, 6]
def baseStart_484177 : Nat := 118140960795 + 484177 * 2 ^ 59
def prefixEnd_484177 : Nat := 4983230072969 + 3 ^ 40 * 484177 * 2
def baseEnd_484177 : Nat := 24554619540943939650451

theorem tailTrace_484177 : CollatzResearch.WordTrace tailWord_484177 prefixEnd_484177 24554619540943939650451 := by
  unfold tailWord_484177
  simp only [CollatzResearch.WordTrace]
  refine ⟨17659385966916894693354785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11772923977944596462236523 17659385966916894693354785)
  ·
    refine ⟨13244539475187671020016089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17659385966916894693354785 13244539475187671020016089)
    ·
      refine ⟨9933404606390753265012067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13244539475187671020016089 9933404606390753265012067)
      ·
        refine ⟨14900106909586129897518101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9933404606390753265012067 14900106909586129897518101)
        ·
          refine ⟨698442511386849838946161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14900106909586129897518101 698442511386849838946161)
          ·
            refine ⟨523831883540137379209621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 698442511386849838946161 523831883540137379209621)
            ·
              refine ⟨24554619540943939650451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 523831883540137379209621 24554619540943939650451)
              ·
                rfl

theorem cell20_484177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 6].length) (baseStart_484177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484177 prefixEnd_484177 := by exact prefixLift 484177
  have htrace : WordTrace (prefixWord ++ tailWord_484177) baseStart_484177 baseEnd_484177 := by
    simpa [prefixWord, tailWord_484177, baseEnd_484177] using wordTrace_append hprefix tailTrace_484177
  have hstable : (prefixWord ++ tailWord_484177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484177).length < 2 ^ (prefixWord ++ tailWord_484177).sum := by decide
  have hdescent : baseEnd_484177 < baseStart_484177 := by decide
  rcases family_descends (prefixWord ++ tailWord_484177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484194 : List Nat := [3, 3, 2, 1, 3, 1, 2, 5]
def baseStart_484194 : Nat := 118140960795 + 484194 * 2 ^ 59
def prefixEnd_484194 : Nat := 4983230072969 + 3 ^ 40 * 484194 * 2
def baseEnd_484194 : Nat := 73666445043906317762441

theorem tailTrace_484194 : CollatzResearch.WordTrace tailWord_484194 prefixEnd_484194 73666445043906317762441 := by
  unfold tailWord_484194
  simp only [CollatzResearch.WordTrace]
  refine ⟨4415001501963826649180909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11773337338570204397815757 4415001501963826649180909)
  ·
    refine ⟨1655625563236434993442841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4415001501963826649180909 1655625563236434993442841)
    ·
      refine ⟨1241719172427326245082131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1655625563236434993442841 1241719172427326245082131)
      ·
        refine ⟨1862578758640989367623197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1241719172427326245082131 1862578758640989367623197)
        ·
          refine ⟨698467034490371012858699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1862578758640989367623197 698467034490371012858699)
          ·
            refine ⟨1047700551735556519288049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698467034490371012858699 1047700551735556519288049)
            ·
              refine ⟨785775413801667389466037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1047700551735556519288049 785775413801667389466037)
              ·
                refine ⟨73666445043906317762441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 785775413801667389466037 73666445043906317762441)
                ·
                  rfl

theorem cell20_484194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_484194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484194 prefixEnd_484194 := by exact prefixLift 484194
  have htrace : WordTrace (prefixWord ++ tailWord_484194) baseStart_484194 baseEnd_484194 := by
    simpa [prefixWord, tailWord_484194, baseEnd_484194] using wordTrace_append hprefix tailTrace_484194
  have hstable : (prefixWord ++ tailWord_484194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484194).length < 2 ^ (prefixWord ++ tailWord_484194).sum := by decide
  have hdescent : baseEnd_484194 < baseStart_484194 := by decide
  rcases family_descends (prefixWord ++ tailWord_484194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484242 : List Nat := [3, 2, 3, 2, 2, 1, 1, 4, 2]
def baseStart_484242 : Nat := 118140960795 + 484242 * 2 ^ 59
def prefixEnd_484242 : Nat := 4983230072969 + 3 ^ 40 * 484242 * 2
def baseEnd_484242 : Nat := 221021243639644119687127

theorem tailTrace_484242 : CollatzResearch.WordTrace tailWord_484242 prefixEnd_484242 221021243639644119687127 := by
  unfold tailWord_484242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4415439177920352698617745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11774504474454273862980653 4415439177920352698617745)
  ·
    refine ⟨3311579383440264523963309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4415439177920352698617745 3311579383440264523963309)
    ·
      refine ⟨1241842268790099196486241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3311579383440264523963309 1241842268790099196486241)
      ·
        refine ⟨931381701592574397364681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1241842268790099196486241 931381701592574397364681)
        ·
          refine ⟨698536276194430798023511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 931381701592574397364681 698536276194430798023511)
          ·
            refine ⟨1047804414291646197035267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698536276194430798023511 1047804414291646197035267)
            ·
              refine ⟨1571706621437469295552901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047804414291646197035267 1571706621437469295552901)
              ·
                refine ⟨294694991519525492916169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1571706621437469295552901 294694991519525492916169)
                ·
                  refine ⟨221021243639644119687127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294694991519525492916169 221021243639644119687127)
                  ·
                    rfl

theorem cell20_484242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_484242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484242 prefixEnd_484242 := by exact prefixLift 484242
  have htrace : WordTrace (prefixWord ++ tailWord_484242) baseStart_484242 baseEnd_484242 := by
    simpa [prefixWord, tailWord_484242, baseEnd_484242] using wordTrace_append hprefix tailTrace_484242
  have hstable : (prefixWord ++ tailWord_484242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484242).length < 2 ^ (prefixWord ++ tailWord_484242).sum := by decide
  have hdescent : baseEnd_484242 < baseStart_484242 := by decide
  rcases family_descends (prefixWord ++ tailWord_484242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484260 : List Nat := [2, 3, 1, 2, 1, 2, 1, 5, 3]
def baseStart_484260 : Nat := 118140960795 + 484260 * 2 ^ 59
def prefixEnd_484260 : Nat := 4983230072969 + 3 ^ 40 * 484260 * 2
def baseEnd_484260 : Nat := 221029459330116057087053

theorem tailTrace_484260 : CollatzResearch.WordTrace tailWord_484260 prefixEnd_484260 221029459330116057087053 := by
  unfold tailWord_484260
  simp only [CollatzResearch.WordTrace]
  refine ⟨8831206612808099934313117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11774942150410799912417489 8831206612808099934313117)
  ·
    refine ⟨3311702479803037475367419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8831206612808099934313117 3311702479803037475367419)
    ·
      refine ⟨4967553719704556213051129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3311702479803037475367419 4967553719704556213051129)
      ·
        refine ⟨3725665289778417159788347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4967553719704556213051129 3725665289778417159788347)
        ·
          refine ⟨5588497934667625739682521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3725665289778417159788347 5588497934667625739682521)
          ·
            refine ⟨4191373451000719304761891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5588497934667625739682521 4191373451000719304761891)
            ·
              refine ⟨6287060176501078957142837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4191373451000719304761891 6287060176501078957142837)
              ·
                refine ⟨589411891546976152232141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6287060176501078957142837 589411891546976152232141)
                ·
                  refine ⟨221029459330116057087053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 589411891546976152232141 221029459330116057087053)
                  ·
                    rfl

theorem cell20_484260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_484260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484260 prefixEnd_484260 := by exact prefixLift 484260
  have htrace : WordTrace (prefixWord ++ tailWord_484260) baseStart_484260 baseEnd_484260 := by
    simpa [prefixWord, tailWord_484260, baseEnd_484260] using wordTrace_append hprefix tailTrace_484260
  have hstable : (prefixWord ++ tailWord_484260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484260).length < 2 ^ (prefixWord ++ tailWord_484260).sum := by decide
  have hdescent : baseEnd_484260 < baseStart_484260 := by decide
  rcases family_descends (prefixWord ++ tailWord_484260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484305 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 4]
def baseStart_484305 : Nat := 118140960795 + 484305 * 2 ^ 59
def prefixEnd_484305 : Nat := 4983230072969 + 3 ^ 40 * 484305 * 2
def baseEnd_484305 : Nat := 221049998556295900586869

theorem tailTrace_484305 : CollatzResearch.WordTrace tailWord_484305 prefixEnd_484305 221049998556295900586869 := by
  unfold tailWord_484305
  simp only [CollatzResearch.WordTrace]
  refine ⟨17664054510453172554014369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11776036340302115036009579 17664054510453172554014369)
  ·
    refine ⟨13248040882839879415510777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17664054510453172554014369 13248040882839879415510777)
    ·
      refine ⟨9936030662129909561633083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13248040882839879415510777 9936030662129909561633083)
      ·
        refine ⟨14904045993194864342449625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9936030662129909561633083 14904045993194864342449625)
        ·
          refine ⟨11178034494896148256837219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14904045993194864342449625 11178034494896148256837219)
          ·
            refine ⟨16767051742344222385255829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11178034494896148256837219 16767051742344222385255829)
            ·
              refine ⟨785955550422385424308867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16767051742344222385255829 785955550422385424308867)
              ·
                refine ⟨1178933325633578136463301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785955550422385424308867 1178933325633578136463301)
                ·
                  refine ⟨221049998556295900586869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1178933325633578136463301 221049998556295900586869)
                  ·
                    rfl

theorem cell20_484305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_484305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484305 prefixEnd_484305 := by exact prefixLift 484305
  have htrace : WordTrace (prefixWord ++ tailWord_484305) baseStart_484305 baseEnd_484305 := by
    simpa [prefixWord, tailWord_484305, baseEnd_484305] using wordTrace_append hprefix tailTrace_484305
  have hstable : (prefixWord ++ tailWord_484305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484305).length < 2 ^ (prefixWord ++ tailWord_484305).sum := by decide
  have hdescent : baseEnd_484305 < baseStart_484305 := by decide
  rcases family_descends (prefixWord ++ tailWord_484305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484325 : List Nat := [1, 3, 1, 6, 1, 2, 2, 4]
def baseStart_484325 : Nat := 118140960795 + 484325 * 2 ^ 59
def prefixEnd_484325 : Nat := 4983230072969 + 3 ^ 40 * 484325 * 2
def baseEnd_484325 : Nat := 73686375700421573306707

theorem tailTrace_484325 : CollatzResearch.WordTrace tailWord_484325 prefixEnd_484325 73686375700421573306707 := by
  unfold tailWord_484325
  simp only [CollatzResearch.WordTrace]
  refine ⟨17664783970380715969742429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11776522646920477313161619 17664783970380715969742429)
  ·
    refine ⟨6624293988892768488653411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17664783970380715969742429 6624293988892768488653411)
    ·
      refine ⟨9936440983339152732980117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6624293988892768488653411 9936440983339152732980117)
      ·
        refine ⟨465770671094022784358443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9936440983339152732980117 465770671094022784358443)
        ·
          refine ⟨698656006641034176537665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465770671094022784358443 698656006641034176537665)
          ·
            refine ⟨523992004980775632403249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 698656006641034176537665 523992004980775632403249)
            ·
              refine ⟨392994003735581724302437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523992004980775632403249 392994003735581724302437)
              ·
                refine ⟨73686375700421573306707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 392994003735581724302437 73686375700421573306707)
                ·
                  rfl

theorem cell20_484325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 4].length) (baseStart_484325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484325 prefixEnd_484325 := by exact prefixLift 484325
  have htrace : WordTrace (prefixWord ++ tailWord_484325) baseStart_484325 baseEnd_484325 := by
    simpa [prefixWord, tailWord_484325, baseEnd_484325] using wordTrace_append hprefix tailTrace_484325
  have hstable : (prefixWord ++ tailWord_484325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484325).length < 2 ^ (prefixWord ++ tailWord_484325).sum := by decide
  have hdescent : baseEnd_484325 < baseStart_484325 := by decide
  rcases family_descends (prefixWord ++ tailWord_484325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484357 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 5]
def baseStart_484357 : Nat := 118140960795 + 484357 * 2 ^ 59
def prefixEnd_484357 : Nat := 4983230072969 + 3 ^ 40 * 484357 * 2
def baseEnd_484357 : Nat := 221073732773214830853323

theorem tailTrace_484357 : CollatzResearch.WordTrace tailWord_484357 prefixEnd_484357 221073732773214830853323 := by
  unfold tailWord_484357
  simp only [CollatzResearch.WordTrace]
  refine ⟨17665951106264785434907325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11777300737509856956604883 17665951106264785434907325)
  ·
    refine ⟨6624731664849294538090247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17665951106264785434907325 6624731664849294538090247)
    ·
      refine ⟨9937097497273941807135371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6624731664849294538090247 9937097497273941807135371)
      ·
        refine ⟨14905646245910912710703057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9937097497273941807135371 14905646245910912710703057)
        ·
          refine ⟨11179234684433184533027293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14905646245910912710703057 11179234684433184533027293)
          ·
            refine ⟨4192213006662444199885235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11179234684433184533027293 4192213006662444199885235)
            ·
              refine ⟨6288319509993666299827853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192213006662444199885235 6288319509993666299827853)
              ·
                refine ⟨2358119816247624862435445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6288319509993666299827853 2358119816247624862435445)
                ·
                  refine ⟨221073732773214830853323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2358119816247624862435445 221073732773214830853323)
                  ·
                    rfl

theorem cell20_484357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_484357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484357 prefixEnd_484357 := by exact prefixLift 484357
  have htrace : WordTrace (prefixWord ++ tailWord_484357) baseStart_484357 baseEnd_484357 := by
    simpa [prefixWord, tailWord_484357, baseEnd_484357] using wordTrace_append hprefix tailTrace_484357
  have hstable : (prefixWord ++ tailWord_484357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484357).length < 2 ^ (prefixWord ++ tailWord_484357).sum := by decide
  have hdescent : baseEnd_484357 < baseStart_484357 := by decide
  rcases family_descends (prefixWord ++ tailWord_484357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484360 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 4]
def baseStart_484360 : Nat := 118140960795 + 484360 * 2 ^ 59
def prefixEnd_484360 : Nat := 4983230072969 + 3 ^ 40 * 484360 * 2
def baseEnd_484360 : Nat := 221075102054960153753311

theorem tailTrace_484360 : CollatzResearch.WordTrace tailWord_484360 prefixEnd_484360 221075102054960153753311 := by
  unfold tailWord_484360
  simp only [CollatzResearch.WordTrace]
  refine ⟨8833030262626958473633267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11777373683502611298177689 8833030262626958473633267)
  ·
    refine ⟨13249545393940437710449901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8833030262626958473633267 13249545393940437710449901)
    ·
      refine ⟨4968579522727664141418713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13249545393940437710449901 4968579522727664141418713)
      ·
        refine ⟨3726434642045748106064035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4968579522727664141418713 3726434642045748106064035)
        ·
          refine ⟨5589651963068622159096053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3726434642045748106064035 5589651963068622159096053)
          ·
            refine ⟨524029871537683327415255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5589651963068622159096053 524029871537683327415255)
            ·
              refine ⟨786044807306524991122883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524029871537683327415255 786044807306524991122883)
              ·
                refine ⟨1179067210959787486684325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786044807306524991122883 1179067210959787486684325)
                ·
                  refine ⟨221075102054960153753311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1179067210959787486684325 221075102054960153753311)
                  ·
                    rfl

theorem cell20_484360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_484360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484360 prefixEnd_484360 := by exact prefixLift 484360
  have htrace : WordTrace (prefixWord ++ tailWord_484360) baseStart_484360 baseEnd_484360 := by
    simpa [prefixWord, tailWord_484360, baseEnd_484360] using wordTrace_append hprefix tailTrace_484360
  have hstable : (prefixWord ++ tailWord_484360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484360).length < 2 ^ (prefixWord ++ tailWord_484360).sum := by decide
  have hdescent : baseEnd_484360 < baseStart_484360 := by decide
  rcases family_descends (prefixWord ++ tailWord_484360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484412 : List Nat := [2, 2, 2, 2, 2, 2, 1, 4, 3]
def baseStart_484412 : Nat := 118140960795 + 484412 * 2 ^ 59
def prefixEnd_484412 : Nat := 4983230072969 + 3 ^ 40 * 484412 * 2
def baseEnd_484412 : Nat := 221098836271879084019765

theorem tailTrace_484412 : CollatzResearch.WordTrace tailWord_484412 prefixEnd_484412 221098836271879084019765 := by
  unfold tailWord_484412
  simp only [CollatzResearch.WordTrace]
  refine ⟨8833978560532764914079745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11778638080710353218772993 8833978560532764914079745)
  ·
    refine ⟨6625483920399573685559809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8833978560532764914079745 6625483920399573685559809)
    ·
      refine ⟨4969112940299680264169857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6625483920399573685559809 4969112940299680264169857)
      ·
        refine ⟨3726834705224760198127393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4969112940299680264169857 3726834705224760198127393)
        ·
          refine ⟨2795126028918570148595545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3726834705224760198127393 2795126028918570148595545)
          ·
            refine ⟨2096344521688927611446659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2795126028918570148595545 2096344521688927611446659)
            ·
              refine ⟨3144516782533391417169989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096344521688927611446659 3144516782533391417169989)
              ·
                refine ⟨589596896725010890719373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3144516782533391417169989 589596896725010890719373)
                ·
                  refine ⟨221098836271879084019765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 589596896725010890719373 221098836271879084019765)
                  ·
                    rfl

theorem cell20_484412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_484412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484412 prefixEnd_484412 := by exact prefixLift 484412
  have htrace : WordTrace (prefixWord ++ tailWord_484412) baseStart_484412 baseEnd_484412 := by
    simpa [prefixWord, tailWord_484412, baseEnd_484412] using wordTrace_append hprefix tailTrace_484412
  have hstable : (prefixWord ++ tailWord_484412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484412).length < 2 ^ (prefixWord ++ tailWord_484412).sum := by decide
  have hdescent : baseEnd_484412 < baseStart_484412 := by decide
  rcases family_descends (prefixWord ++ tailWord_484412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484422 : List Nat := [6, 1, 1, 1, 1, 2, 3, 5]
def baseStart_484422 : Nat := 118140960795 + 484422 * 2 ^ 59
def prefixEnd_484422 : Nat := 4983230072969 + 3 ^ 40 * 484422 * 2
def baseEnd_484422 : Nat := 73701133514787831228797

theorem tailTrace_484422 : CollatzResearch.WordTrace tailWord_484422 prefixEnd_484422 73701133514787831228797 := by
  unfold tailWord_484422
  simp only [CollatzResearch.WordTrace]
  refine ⟨552135057844665673000735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11778881234019534357349013 552135057844665673000735)
  ·
    refine ⟨828202586766998509501103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 552135057844665673000735 828202586766998509501103)
    ·
      refine ⟨1242303880150497764251655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 828202586766998509501103 1242303880150497764251655)
      ·
        refine ⟨1863455820225746646377483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242303880150497764251655 1863455820225746646377483)
        ·
          refine ⟨2795183730338619969566225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1863455820225746646377483 2795183730338619969566225)
          ·
            refine ⟨2096387797753964977174669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2795183730338619969566225 2096387797753964977174669)
            ·
              refine ⟨786145424157736866440501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2096387797753964977174669 786145424157736866440501)
              ·
                refine ⟨73701133514787831228797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 786145424157736866440501 73701133514787831228797)
                ·
                  rfl

theorem cell20_484422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_484422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484422 prefixEnd_484422 := by exact prefixLift 484422
  have htrace : WordTrace (prefixWord ++ tailWord_484422) baseStart_484422 baseEnd_484422 := by
    simpa [prefixWord, tailWord_484422, baseEnd_484422] using wordTrace_append hprefix tailTrace_484422
  have hstable : (prefixWord ++ tailWord_484422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484422).length < 2 ^ (prefixWord ++ tailWord_484422).sum := by decide
  have hdescent : baseEnd_484422 < baseStart_484422 := by decide
  rcases family_descends (prefixWord ++ tailWord_484422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484426 : List Nat := [3, 1, 2, 1, 1, 2, 5, 5]
def baseStart_484426 : Nat := 118140960795 + 484426 * 2 ^ 59
def prefixEnd_484426 : Nat := 4983230072969 + 3 ^ 40 * 484426 * 2
def baseEnd_484426 : Nat := 73701742084452419184347

theorem tailTrace_484426 : CollatzResearch.WordTrace tailWord_484426 prefixEnd_484426 73701742084452419184347 := by
  unfold tailWord_484426
  simp only [CollatzResearch.WordTrace]
  refine ⟨4417116935753702554792283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11778978495343206812779421 4417116935753702554792283)
  ·
    refine ⟨6625675403630553832188425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4417116935753702554792283 6625675403630553832188425)
    ·
      refine ⟨4969256552722915374141319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6625675403630553832188425 4969256552722915374141319)
      ·
        refine ⟨7453884829084373061211979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4969256552722915374141319 7453884829084373061211979)
        ·
          refine ⟨11180827243626559591817969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7453884829084373061211979 11180827243626559591817969)
          ·
            refine ⟨8385620432719919693863477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11180827243626559591817969 8385620432719919693863477)
            ·
              refine ⟨786151915567492471299701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8385620432719919693863477 786151915567492471299701)
              ·
                refine ⟨73701742084452419184347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 786151915567492471299701 73701742084452419184347)
                ·
                  rfl

theorem cell20_484426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_484426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484426 prefixEnd_484426 := by exact prefixLift 484426
  have htrace : WordTrace (prefixWord ++ tailWord_484426) baseStart_484426 baseEnd_484426 := by
    simpa [prefixWord, tailWord_484426, baseEnd_484426] using wordTrace_append hprefix tailTrace_484426
  have hstable : (prefixWord ++ tailWord_484426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484426).length < 2 ^ (prefixWord ++ tailWord_484426).sum := by decide
  have hdescent : baseEnd_484426 < baseStart_484426 := by decide
  rcases family_descends (prefixWord ++ tailWord_484426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484429 : List Nat := [1, 6, 1, 1, 1, 2, 2, 3, 3]
def baseStart_484429 : Nat := 118140960795 + 484429 * 2 ^ 59
def prefixEnd_484429 : Nat := 4983230072969 + 3 ^ 40 * 484429 * 2
def baseEnd_484429 : Nat := 221106595535102580453029

theorem tailTrace_484429 : CollatzResearch.WordTrace tailWord_484429 prefixEnd_484429 221106595535102580453029 := by
  unfold tailWord_484429
  simp only [CollatzResearch.WordTrace]
  refine ⟨17668577162003941731528341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11779051441335961154352227 17668577162003941731528341)
  ·
    refine ⟨828214554468934768665391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17668577162003941731528341 828214554468934768665391)
    ·
      refine ⟨1242321831703402152998087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 828214554468934768665391 1242321831703402152998087)
      ·
        refine ⟨1863482747555103229497131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242321831703402152998087 1863482747555103229497131)
        ·
          refine ⟨2795224121332654844245697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1863482747555103229497131 2795224121332654844245697)
          ·
            refine ⟨2096418090999491133184273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2795224121332654844245697 2096418090999491133184273)
            ·
              refine ⟨1572313568249618349888205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2096418090999491133184273 1572313568249618349888205)
              ·
                refine ⟨589617588093606881208077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1572313568249618349888205 589617588093606881208077)
                ·
                  refine ⟨221106595535102580453029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 589617588093606881208077 221106595535102580453029)
                  ·
                    rfl

theorem cell20_484429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_484429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484429 prefixEnd_484429 := by exact prefixLift 484429
  have htrace : WordTrace (prefixWord ++ tailWord_484429) baseStart_484429 baseEnd_484429 := by
    simpa [prefixWord, tailWord_484429, baseEnd_484429] using wordTrace_append hprefix tailTrace_484429
  have hstable : (prefixWord ++ tailWord_484429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484429).length < 2 ^ (prefixWord ++ tailWord_484429).sum := by decide
  have hdescent : baseEnd_484429 < baseStart_484429 := by decide
  rcases family_descends (prefixWord ++ tailWord_484429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484471 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 5]
def baseStart_484471 : Nat := 118140960795 + 484471 * 2 ^ 59
def prefixEnd_484471 : Nat := 4983230072969 + 3 ^ 40 * 484471 * 2
def baseEnd_484471 : Nat := 221125765479537101052857

theorem tailTrace_484471 : CollatzResearch.WordTrace tailWord_484471 prefixEnd_484471 221125765479537101052857 := by
  unfold tailWord_484471
  simp only [CollatzResearch.WordTrace]
  refine ⟨17670109027851782904557267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11780072685234521936371511 17670109027851782904557267)
  ·
    refine ⟨26505163541777674356835901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17670109027851782904557267 26505163541777674356835901)
    ·
      refine ⟨9939436328166627883813463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26505163541777674356835901 9939436328166627883813463)
      ·
        refine ⟨14909154492249941825720195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9939436328166627883813463 14909154492249941825720195)
        ·
          refine ⟨22363731738374912738580293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14909154492249941825720195 22363731738374912738580293)
          ·
            refine ⟨4193199700945296138483805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22363731738374912738580293 4193199700945296138483805)
            ·
              refine ⟨1572449887854486051931427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4193199700945296138483805 1572449887854486051931427)
              ·
                refine ⟨2358674831781729077897141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1572449887854486051931427 2358674831781729077897141)
                ·
                  refine ⟨221125765479537101052857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2358674831781729077897141 221125765479537101052857)
                  ·
                    rfl

theorem cell20_484471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_484471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484471 prefixEnd_484471 := by exact prefixLift 484471
  have htrace : WordTrace (prefixWord ++ tailWord_484471) baseStart_484471 baseEnd_484471 := by
    simpa [prefixWord, tailWord_484471, baseEnd_484471] using wordTrace_append hprefix tailTrace_484471
  have hstable : (prefixWord ++ tailWord_484471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484471).length < 2 ^ (prefixWord ++ tailWord_484471).sum := by decide
  have hdescent : baseEnd_484471 < baseStart_484471 := by decide
  rcases family_descends (prefixWord ++ tailWord_484471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484498 : List Nat := [3, 2, 3, 1, 1, 4, 2, 4]
def baseStart_484498 : Nat := 118140960795 + 484498 * 2 ^ 59
def prefixEnd_484498 : Nat := 4983230072969 + 3 ^ 40 * 484498 * 2
def baseEnd_484498 : Nat := 73712696338415002384249

theorem tailTrace_484498 : CollatzResearch.WordTrace tailWord_484498 prefixEnd_484498 73712696338415002384249 := by
  unfold tailWord_484498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4417773449688491628947537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11780729199169311010526765 4417773449688491628947537)
  ·
    refine ⟨3313330087266368721710653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4417773449688491628947537 3313330087266368721710653)
    ·
      refine ⟨1242498782724888270641495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3313330087266368721710653 1242498782724888270641495)
      ·
        refine ⟨1863748174087332405962243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242498782724888270641495 1863748174087332405962243)
        ·
          refine ⟨2795622261130998608943365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1863748174087332405962243 2795622261130998608943365)
          ·
            refine ⟨524179173962062239176881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2795622261130998608943365 524179173962062239176881)
            ·
              refine ⟨393134380471546679382661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524179173962062239176881 393134380471546679382661)
              ·
                refine ⟨73712696338415002384249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 393134380471546679382661 73712696338415002384249)
                ·
                  rfl

theorem cell20_484498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_484498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484498 prefixEnd_484498 := by exact prefixLift 484498
  have htrace : WordTrace (prefixWord ++ tailWord_484498) baseStart_484498 baseEnd_484498 := by
    simpa [prefixWord, tailWord_484498, baseEnd_484498] using wordTrace_append hprefix tailTrace_484498
  have hstable : (prefixWord ++ tailWord_484498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484498).length < 2 ^ (prefixWord ++ tailWord_484498).sum := by decide
  have hdescent : baseEnd_484498 < baseStart_484498 := by decide
  rcases family_descends (prefixWord ++ tailWord_484498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484509 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 7]
def baseStart_484509 : Nat := 118140960795 + 484509 * 2 ^ 59
def prefixEnd_484509 : Nat := 4983230072969 + 3 ^ 40 * 484509 * 2
def baseEnd_484509 : Nat := 221143109714977857786035

theorem tailTrace_484509 : CollatzResearch.WordTrace tailWord_484509 prefixEnd_484509 221143109714977857786035 := by
  unfold tailWord_484509
  simp only [CollatzResearch.WordTrace]
  refine ⟨17671495001714115394440581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11780996667809410262960387 17671495001714115394440581)
  ·
    refine ⟨3313405312821396636457609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17671495001714115394440581 3313405312821396636457609)
    ·
      refine ⟨2485053984616047477343207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3313405312821396636457609 2485053984616047477343207)
      ·
        refine ⟨3727580976924071216014811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2485053984616047477343207 3727580976924071216014811)
        ·
          refine ⟨5591371465386106824022217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3727580976924071216014811 5591371465386106824022217)
          ·
            refine ⟨4193528599039580118016663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5591371465386106824022217 4193528599039580118016663)
            ·
              refine ⟨6290292898559370177024995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4193528599039580118016663 6290292898559370177024995)
              ·
                refine ⟨9435439347839055265537493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6290292898559370177024995 9435439347839055265537493)
                ·
                  refine ⟨221143109714977857786035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9435439347839055265537493 221143109714977857786035)
                  ·
                    rfl

theorem cell20_484509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_484509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484509 prefixEnd_484509 := by exact prefixLift 484509
  have htrace : WordTrace (prefixWord ++ tailWord_484509) baseStart_484509 baseEnd_484509 := by
    simpa [prefixWord, tailWord_484509, baseEnd_484509] using wordTrace_append hprefix tailTrace_484509
  have hstable : (prefixWord ++ tailWord_484509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484509).length < 2 ^ (prefixWord ++ tailWord_484509).sum := by decide
  have hdescent : baseEnd_484509 < baseStart_484509 := by decide
  rcases family_descends (prefixWord ++ tailWord_484509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484519 : List Nat := [1, 1, 6, 2, 1, 3, 6]
def baseStart_484519 : Nat := 118140960795 + 484519 * 2 ^ 59
def prefixEnd_484519 : Nat := 4983230072969 + 3 ^ 40 * 484519 * 2
def baseEnd_484519 : Nat := 24571963776384696383629

theorem tailTrace_484519 : CollatzResearch.WordTrace tailWord_484519 prefixEnd_484519 24571963776384696383629 := by
  unfold tailWord_484519
  simp only [CollatzResearch.WordTrace]
  refine ⟨17671859731677887102304611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11781239821118591401536407 17671859731677887102304611)
  ·
    refine ⟨26507789597516830653456917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17671859731677887102304611 26507789597516830653456917)
    ·
      refine ⟨1242552637383601436880793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26507789597516830653456917 1242552637383601436880793)
      ·
        refine ⟨931914478037701077660595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1242552637383601436880793 931914478037701077660595)
        ·
          refine ⟨1397871717056551616490893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931914478037701077660595 1397871717056551616490893)
          ·
            refine ⟨524201893896206856184085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1397871717056551616490893 524201893896206856184085)
            ·
              refine ⟨24571963776384696383629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 524201893896206856184085 24571963776384696383629)
              ·
                rfl

theorem cell20_484519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 6].length) (baseStart_484519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484519 prefixEnd_484519 := by exact prefixLift 484519
  have htrace : WordTrace (prefixWord ++ tailWord_484519) baseStart_484519 baseEnd_484519 := by
    simpa [prefixWord, tailWord_484519, baseEnd_484519] using wordTrace_append hprefix tailTrace_484519
  have hstable : (prefixWord ++ tailWord_484519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484519).length < 2 ^ (prefixWord ++ tailWord_484519).sum := by decide
  have hdescent : baseEnd_484519 < baseStart_484519 := by decide
  rcases family_descends (prefixWord ++ tailWord_484519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484540 : List Nat := [2, 2, 2, 3, 2, 1, 1, 7]
def baseStart_484540 : Nat := 118140960795 + 484540 * 2 ^ 59
def prefixEnd_484540 : Nat := 4983230072969 + 3 ^ 40 * 484540 * 2
def baseEnd_484540 : Nat := 73719086319893175917525

theorem tailTrace_484540 : CollatzResearch.WordTrace tailWord_484540 prefixEnd_484540 73719086319893175917525 := by
  unfold tailWord_484540
  simp only [CollatzResearch.WordTrace]
  refine ⟨8836312832300903844409537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11781750443067871792546049 8836312832300903844409537)
  ·
    refine ⟨6627234624225677883307153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8836312832300903844409537 6627234624225677883307153)
    ·
      refine ⟨4970425968169258412480365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6627234624225677883307153 4970425968169258412480365)
      ·
        refine ⟨1863909738063471904680137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4970425968169258412480365 1863909738063471904680137)
        ·
          refine ⟨1397932303547603928510103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1863909738063471904680137 1397932303547603928510103)
          ·
            refine ⟨2096898455321405892765155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397932303547603928510103 2096898455321405892765155)
            ·
              refine ⟨3145347682982108839147733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096898455321405892765155 3145347682982108839147733)
              ·
                refine ⟨73719086319893175917525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3145347682982108839147733 73719086319893175917525)
                ·
                  rfl

theorem cell20_484540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_484540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484540 prefixEnd_484540 := by exact prefixLift 484540
  have htrace : WordTrace (prefixWord ++ tailWord_484540) baseStart_484540 baseEnd_484540 := by
    simpa [prefixWord, tailWord_484540, baseEnd_484540] using wordTrace_append hprefix tailTrace_484540
  have hstable : (prefixWord ++ tailWord_484540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484540).length < 2 ^ (prefixWord ++ tailWord_484540).sum := by decide
  have hdescent : baseEnd_484540 < baseStart_484540 := by decide
  rcases family_descends (prefixWord ++ tailWord_484540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484581 : List Nat := [1, 3, 1, 4, 3, 1, 2, 2, 3]
def baseStart_484581 : Nat := 118140960795 + 484581 * 2 ^ 59
def prefixEnd_484581 : Nat := 4983230072969 + 3 ^ 40 * 484581 * 2
def baseEnd_484581 : Nat := 221175972476865607385741

theorem tailTrace_484581 : CollatzResearch.WordTrace tailWord_484581 prefixEnd_484581 221175972476865607385741 := by
  unfold tailWord_484581
  simp only [CollatzResearch.WordTrace]
  refine ⟨17674121057453271691061597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11782747371635514460707731 17674121057453271691061597)
  ·
    refine ⟨6627795396544976884148099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17674121057453271691061597 6627795396544976884148099)
    ·
      refine ⟨9941693094817465326222149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6627795396544976884148099 9941693094817465326222149)
      ·
        refine ⟨1864067455278274748666653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9941693094817465326222149 1864067455278274748666653)
        ·
          refine ⟨699025295729353030749995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1864067455278274748666653 699025295729353030749995)
          ·
            refine ⟨1048537943594029546124993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699025295729353030749995 1048537943594029546124993)
            ·
              refine ⟨786403457695522159593745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048537943594029546124993 786403457695522159593745)
              ·
                refine ⟨589802593271641619695309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 786403457695522159593745 589802593271641619695309)
                ·
                  refine ⟨221175972476865607385741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 589802593271641619695309 221175972476865607385741)
                  ·
                    rfl

theorem cell20_484581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_484581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484581 prefixEnd_484581 := by exact prefixLift 484581
  have htrace : WordTrace (prefixWord ++ tailWord_484581) baseStart_484581 baseEnd_484581 := by
    simpa [prefixWord, tailWord_484581, baseEnd_484581] using wordTrace_append hprefix tailTrace_484581
  have hstable : (prefixWord ++ tailWord_484581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484581).length < 2 ^ (prefixWord ++ tailWord_484581).sum := by decide
  have hdescent : baseEnd_484581 < baseStart_484581 := by decide
  rcases family_descends (prefixWord ++ tailWord_484581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484588 : List Nat := [2, 2, 1, 1, 2, 5, 1, 4, 2]
def baseStart_484588 : Nat := 118140960795 + 484588 * 2 ^ 59
def prefixEnd_484588 : Nat := 4983230072969 + 3 ^ 40 * 484588 * 2
def baseEnd_484588 : Nat := 221179167467604694152379

theorem tailTrace_484588 : CollatzResearch.WordTrace tailWord_484588 prefixEnd_484588 221179167467604694152379 := by
  unfold tailWord_484588
  simp only [CollatzResearch.WordTrace]
  refine ⟨8837188184213955943283209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11782917578951941257710945 8837188184213955943283209)
  ·
    refine ⟨6627891138160466957462407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8837188184213955943283209 6627891138160466957462407)
    ·
      refine ⟨9941836707240700436193611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6627891138160466957462407 9941836707240700436193611)
      ·
        refine ⟨14912755060861050654290417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9941836707240700436193611 14912755060861050654290417)
        ·
          refine ⟨11184566295645787990717813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14912755060861050654290417 11184566295645787990717813)
          ·
            refine ⟨1048553090216792624129795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11184566295645787990717813 1048553090216792624129795)
            ·
              refine ⟨1572829635325188936194693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048553090216792624129795 1572829635325188936194693)
              ·
                refine ⟨294905556623472925536505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1572829635325188936194693 294905556623472925536505)
                ·
                  refine ⟨221179167467604694152379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294905556623472925536505 221179167467604694152379)
                  ·
                    rfl

theorem cell20_484588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_484588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484588 prefixEnd_484588 := by exact prefixLift 484588
  have htrace : WordTrace (prefixWord ++ tailWord_484588) baseStart_484588 baseEnd_484588 := by
    simpa [prefixWord, tailWord_484588, baseEnd_484588] using wordTrace_append hprefix tailTrace_484588
  have hstable : (prefixWord ++ tailWord_484588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484588).length < 2 ^ (prefixWord ++ tailWord_484588).sum := by decide
  have hdescent : baseEnd_484588 < baseStart_484588 := by decide
  rcases family_descends (prefixWord ++ tailWord_484588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484609 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 4]
def baseStart_484609 : Nat := 118140960795 + 484609 * 2 ^ 59
def prefixEnd_484609 : Nat := 4983230072969 + 3 ^ 40 * 484609 * 2
def baseEnd_484609 : Nat := 221188752439821954452293

theorem tailTrace_484609 : CollatzResearch.WordTrace tailWord_484609 prefixEnd_484609 221188752439821954452293 := by
  unfold tailWord_484609
  simp only [CollatzResearch.WordTrace]
  refine ⟨17675142301351832473080881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11783428200901221648720587 17675142301351832473080881)
  ·
    refine ⟨13256356726013874354810661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17675142301351832473080881 13256356726013874354810661)
    ·
      refine ⟨2485566886127601441526999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13256356726013874354810661 2485566886127601441526999)
      ·
        refine ⟨3728350329191402162290499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2485566886127601441526999 3728350329191402162290499)
        ·
          refine ⟨5592525493787103243435749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3728350329191402162290499 5592525493787103243435749)
          ·
            refine ⟨1048598530085081858144203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5592525493787103243435749 1048598530085081858144203)
            ·
              refine ⟨1572897795127622787216305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048598530085081858144203 1572897795127622787216305)
              ·
                refine ⟨1179673346345717090412229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1572897795127622787216305 1179673346345717090412229)
                ·
                  refine ⟨221188752439821954452293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1179673346345717090412229 221188752439821954452293)
                  ·
                    rfl

theorem cell20_484609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_484609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484609 prefixEnd_484609 := by exact prefixLift 484609
  have htrace : WordTrace (prefixWord ++ tailWord_484609) baseStart_484609 baseEnd_484609 := by
    simpa [prefixWord, tailWord_484609, baseEnd_484609] using wordTrace_append hprefix tailTrace_484609
  have hstable : (prefixWord ++ tailWord_484609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484609).length < 2 ^ (prefixWord ++ tailWord_484609).sum := by decide
  have hdescent : baseEnd_484609 < baseStart_484609 := by decide
  rcases family_descends (prefixWord ++ tailWord_484609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484640 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 5]
def baseStart_484640 : Nat := 118140960795 + 484640 * 2 ^ 59
def prefixEnd_484640 : Nat := 4983230072969 + 3 ^ 40 * 484640 * 2
def baseEnd_484640 : Nat := 221202901684523624418833

theorem tailTrace_484640 : CollatzResearch.WordTrace tailWord_484640 prefixEnd_484640 221202901684523624418833 := by
  unfold tailWord_484640
  simp only [CollatzResearch.WordTrace]
  refine ⟨8838136482119762383729687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11784181976159683178306249 8838136482119762383729687)
  ·
    refine ⟨13257204723179643575594531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8838136482119762383729687 13257204723179643575594531)
    ·
      refine ⟨19885807084769465363391797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13257204723179643575594531 19885807084769465363391797)
      ·
        refine ⟨1864294414197137377817981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19885807084769465363391797 1864294414197137377817981)
        ·
          refine ⟨699110405323926516681743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1864294414197137377817981 699110405323926516681743)
          ·
            refine ⟨1048665607985889775022615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699110405323926516681743 1048665607985889775022615)
            ·
              refine ⟨1572998411978834662533923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048665607985889775022615 1572998411978834662533923)
              ·
                refine ⟨2359497617968251993800885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1572998411978834662533923 2359497617968251993800885)
                ·
                  refine ⟨221202901684523624418833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2359497617968251993800885 221202901684523624418833)
                  ·
                    rfl

theorem cell20_484640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_484640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484640 prefixEnd_484640 := by exact prefixLift 484640
  have htrace : WordTrace (prefixWord ++ tailWord_484640) baseStart_484640 baseEnd_484640 := by
    simpa [prefixWord, tailWord_484640, baseEnd_484640] using wordTrace_append hprefix tailTrace_484640
  have hstable : (prefixWord ++ tailWord_484640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484640).length < 2 ^ (prefixWord ++ tailWord_484640).sum := by decide
  have hdescent : baseEnd_484640 < baseStart_484640 := by decide
  rcases family_descends (prefixWord ++ tailWord_484640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484657 : List Nat := [1, 2, 2, 3, 3, 2, 3, 1, 3]
def baseStart_484657 : Nat := 118140960795 + 484657 * 2 ^ 59
def prefixEnd_484657 : Nat := 4983230072969 + 3 ^ 40 * 484657 * 2
def baseEnd_484657 : Nat := 221210660947747120852097

theorem tailTrace_484657 : CollatzResearch.WordTrace tailWord_484657 prefixEnd_484657 221210660947747120852097 := by
  unfold tailWord_484657
  simp only [CollatzResearch.WordTrace]
  refine ⟨17676893005177936670828225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11784595336785291113885483 17676893005177936670828225)
  ·
    refine ⟨13257669753883452503121169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17676893005177936670828225 13257669753883452503121169)
    ·
      refine ⟨9943252315412589377340877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13257669753883452503121169 9943252315412589377340877)
      ·
        refine ⟨3728719618279721016502829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9943252315412589377340877 3728719618279721016502829)
        ·
          refine ⟨1398269856854895381188561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3728719618279721016502829 1398269856854895381188561)
          ·
            refine ⟨1048702392641171535891421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1398269856854895381188561 1048702392641171535891421)
            ·
              refine ⟨393263397240439325959283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1048702392641171535891421 393263397240439325959283)
              ·
                refine ⟨589895095860658988938925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393263397240439325959283 589895095860658988938925)
                ·
                  refine ⟨221210660947747120852097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 589895095860658988938925 221210660947747120852097)
                  ·
                    rfl

theorem cell20_484657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 3].length) (baseStart_484657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484657 prefixEnd_484657 := by exact prefixLift 484657
  have htrace : WordTrace (prefixWord ++ tailWord_484657) baseStart_484657 baseEnd_484657 := by
    simpa [prefixWord, tailWord_484657, baseEnd_484657] using wordTrace_append hprefix tailTrace_484657
  have hstable : (prefixWord ++ tailWord_484657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484657).length < 2 ^ (prefixWord ++ tailWord_484657).sum := by decide
  have hdescent : baseEnd_484657 < baseStart_484657 := by decide
  rcases family_descends (prefixWord ++ tailWord_484657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484671 : List Nat := [1, 1, 2, 2, 4, 4, 2, 4]
def baseStart_484671 : Nat := 118140960795 + 484671 * 2 ^ 59
def prefixEnd_484671 : Nat := 4983230072969 + 3 ^ 40 * 484671 * 2
def baseEnd_484671 : Nat := 73739016976408431461791

theorem tailTrace_484671 : CollatzResearch.WordTrace tailWord_484671 prefixEnd_484671 73739016976408431461791 := by
  unfold tailWord_484671
  simp only [CollatzResearch.WordTrace]
  refine ⟨17677403627127217061837867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11784935751418144707891911 17677403627127217061837867)
  ·
    refine ⟨26516105440690825592756801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17677403627127217061837867 26516105440690825592756801)
    ·
      refine ⟨19887079080518119194567601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26516105440690825592756801 19887079080518119194567601)
      ·
        refine ⟨14915309310388589395925701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19887079080518119194567601 14915309310388589395925701)
        ·
          refine ⟨2796620495697860511736069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14915309310388589395925701 2796620495697860511736069)
          ·
            refine ⟨524366342943348845950513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2796620495697860511736069 524366342943348845950513)
            ·
              refine ⟨393274757207511634462885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524366342943348845950513 393274757207511634462885)
              ·
                refine ⟨73739016976408431461791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 393274757207511634462885 73739016976408431461791)
                ·
                  rfl

theorem cell20_484671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 4].length) (baseStart_484671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484671 prefixEnd_484671 := by exact prefixLift 484671
  have htrace : WordTrace (prefixWord ++ tailWord_484671) baseStart_484671 baseEnd_484671 := by
    simpa [prefixWord, tailWord_484671, baseEnd_484671] using wordTrace_append hprefix tailTrace_484671
  have hstable : (prefixWord ++ tailWord_484671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484671).length < 2 ^ (prefixWord ++ tailWord_484671).sum := by decide
  have hdescent : baseEnd_484671 < baseStart_484671 := by decide
  rcases family_descends (prefixWord ++ tailWord_484671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484694 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_484694 : Nat := 118140960795 + 484694 * 2 ^ 59
def prefixEnd_484694 : Nat := 4983230072969 + 3 ^ 40 * 484694 * 2
def baseEnd_484694 : Nat := 221227548755939436618613

theorem tailTrace_484694 : CollatzResearch.WordTrace tailWord_484694 prefixEnd_484694 221227548755939436618613 := by
  unfold tailWord_484694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104890156627743249370321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11785495004029261326616757 1104890156627743249370321)
  ·
    refine ⟨828667617470807437027741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1104890156627743249370321 828667617470807437027741)
    ·
      refine ⟨310750356551552788885403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 828667617470807437027741 310750356551552788885403)
      ·
        refine ⟨466125534827329183328105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310750356551552788885403 466125534827329183328105)
        ·
          refine ⟨349594151120496887496079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466125534827329183328105 349594151120496887496079)
          ·
            refine ⟨524391226680745331244119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349594151120496887496079 524391226680745331244119)
            ·
              refine ⟨786586840021117996866179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524391226680745331244119 786586840021117996866179)
              ·
                refine ⟨1179880260031676995299269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786586840021117996866179 1179880260031676995299269)
                ·
                  refine ⟨221227548755939436618613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1179880260031676995299269 221227548755939436618613)
                  ·
                    rfl

theorem cell20_484694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_484694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484694 prefixEnd_484694 := by exact prefixLift 484694
  have htrace : WordTrace (prefixWord ++ tailWord_484694) baseStart_484694 baseEnd_484694 := by
    simpa [prefixWord, tailWord_484694, baseEnd_484694] using wordTrace_append hprefix tailTrace_484694
  have hstable : (prefixWord ++ tailWord_484694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484694).length < 2 ^ (prefixWord ++ tailWord_484694).sum := by decide
  have hdescent : baseEnd_484694 < baseStart_484694 := by decide
  rcases family_descends (prefixWord ++ tailWord_484694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484712 : List Nat := [2, 1, 4, 2, 3, 2, 2, 1, 3]
def baseStart_484712 : Nat := 118140960795 + 484712 * 2 ^ 59
def prefixEnd_484712 : Nat := 4983230072969 + 3 ^ 40 * 484712 * 2
def baseEnd_484712 : Nat := 221235764446411374018539

theorem tailTrace_484712 : CollatzResearch.WordTrace tailWord_484712 prefixEnd_484712 221235764446411374018539 := by
  unfold tailWord_484712
  simp only [CollatzResearch.WordTrace]
  refine ⟨8839449509989340532040195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11785932679985787376053593 8839449509989340532040195)
  ·
    refine ⟨13259174264984010798060293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8839449509989340532040195 13259174264984010798060293)
    ·
      refine ⟨2486095174684502024636305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13259174264984010798060293 2486095174684502024636305)
      ·
        refine ⟨1864571381013376518477229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2486095174684502024636305 1864571381013376518477229)
        ·
          refine ⟨699214267880016194428961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1864571381013376518477229 699214267880016194428961)
          ·
            refine ⟨524410700910012145821721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 699214267880016194428961 524410700910012145821721)
            ·
              refine ⟨393308025682509109366291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524410700910012145821721 393308025682509109366291)
              ·
                refine ⟨589962038523763664049437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393308025682509109366291 589962038523763664049437)
                ·
                  refine ⟨221235764446411374018539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 589962038523763664049437 221235764446411374018539)
                  ·
                    rfl

theorem cell20_484712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 3].length) (baseStart_484712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484712 prefixEnd_484712 := by exact prefixLift 484712
  have htrace : WordTrace (prefixWord ++ tailWord_484712) baseStart_484712 baseEnd_484712 := by
    simpa [prefixWord, tailWord_484712, baseEnd_484712] using wordTrace_append hprefix tailTrace_484712
  have hstable : (prefixWord ++ tailWord_484712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484712).length < 2 ^ (prefixWord ++ tailWord_484712).sum := by decide
  have hdescent : baseEnd_484712 < baseStart_484712 := by decide
  rcases family_descends (prefixWord ++ tailWord_484712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484716 : List Nat := [2, 2, 1, 1, 5, 2, 1, 3, 3]
def baseStart_484716 : Nat := 118140960795 + 484716 * 2 ^ 59
def prefixEnd_484716 : Nat := 4983230072969 + 3 ^ 40 * 484716 * 2
def baseEnd_484716 : Nat := 221237590155405137885189

theorem tailTrace_484716 : CollatzResearch.WordTrace tailWord_484716 prefixEnd_484716 221237590155405137885189 := by
  unfold tailWord_484716
  simp only [CollatzResearch.WordTrace]
  refine ⟨8839522455982094873613001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11786029941309459831484001 8839522455982094873613001)
  ·
    refine ⟨6629641841986571155209751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8839522455982094873613001 6629641841986571155209751)
    ·
      refine ⟨9944462762979856732814627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6629641841986571155209751 9944462762979856732814627)
      ·
        refine ⟨14916694144469785099221941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9944462762979856732814627 14916694144469785099221941)
        ·
          refine ⟨1398440076044042353052057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14916694144469785099221941 1398440076044042353052057)
          ·
            refine ⟨1048830057033031764789043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1398440076044042353052057 1048830057033031764789043)
            ·
              refine ⟨1573245085549547647183565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048830057033031764789043 1573245085549547647183565)
              ·
                refine ⟨589966907081080367693837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1573245085549547647183565 589966907081080367693837)
                ·
                  refine ⟨221237590155405137885189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 589966907081080367693837 221237590155405137885189)
                  ·
                    rfl

theorem cell20_484716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_484716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484716 prefixEnd_484716 := by exact prefixLift 484716
  have htrace : WordTrace (prefixWord ++ tailWord_484716) baseStart_484716 baseEnd_484716 := by
    simpa [prefixWord, tailWord_484716, baseEnd_484716] using wordTrace_append hprefix tailTrace_484716
  have hstable : (prefixWord ++ tailWord_484716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484716).length < 2 ^ (prefixWord ++ tailWord_484716).sum := by decide
  have hdescent : baseEnd_484716 < baseStart_484716 := by decide
  rcases family_descends (prefixWord ++ tailWord_484716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484764 : List Nat := [2, 2, 3, 4, 1, 2, 1, 5]
def baseStart_484764 : Nat := 118140960795 + 484764 * 2 ^ 59
def prefixEnd_484764 : Nat := 4983230072969 + 3 ^ 40 * 484764 * 2
def baseEnd_484764 : Nat := 73753166221110101428331

theorem tailTrace_484764 : CollatzResearch.WordTrace tailWord_484764 prefixEnd_484764 73753166221110101428331 := by
  unfold tailWord_484764
  simp only [CollatzResearch.WordTrace]
  refine ⟨8840397807895146972486673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11787197077193529296648897 8840397807895146972486673)
  ·
    refine ⟨6630298355921360229365005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8840397807895146972486673 6630298355921360229365005)
    ·
      refine ⟨2486361883470510086011877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6630298355921360229365005 2486361883470510086011877)
      ·
        refine ⟨466192853150720641127227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2486361883470510086011877 466192853150720641127227)
        ·
          refine ⟨699289279726080961690841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466192853150720641127227 699289279726080961690841)
          ·
            refine ⟨524466959794560721268131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 699289279726080961690841 524466959794560721268131)
            ·
              refine ⟨786700439691841081902197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524466959794560721268131 786700439691841081902197)
              ·
                refine ⟨73753166221110101428331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 786700439691841081902197 73753166221110101428331)
                ·
                  rfl

theorem cell20_484764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_484764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484764 prefixEnd_484764 := by exact prefixLift 484764
  have htrace : WordTrace (prefixWord ++ tailWord_484764) baseStart_484764 baseEnd_484764 := by
    simpa [prefixWord, tailWord_484764, baseEnd_484764] using wordTrace_append hprefix tailTrace_484764
  have hstable : (prefixWord ++ tailWord_484764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484764).length < 2 ^ (prefixWord ++ tailWord_484764).sum := by decide
  have hdescent : baseEnd_484764 < baseStart_484764 := by decide
  rcases family_descends (prefixWord ++ tailWord_484764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484837 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 4]
def baseStart_484837 : Nat := 118140960795 + 484837 * 2 ^ 59
def prefixEnd_484837 : Nat := 4983230072969 + 3 ^ 40 * 484837 * 2
def baseEnd_484837 : Nat := 221292817852466494851361

theorem tailTrace_484837 : CollatzResearch.WordTrace tailWord_484837 prefixEnd_484837 221292817852466494851361 := by
  unfold tailWord_484837
  simp only [CollatzResearch.WordTrace]
  refine ⟨17683458144525827412380765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11788972096350551608253843 17683458144525827412380765)
  ·
    refine ⟨6631296804197185279642787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17683458144525827412380765 6631296804197185279642787)
    ·
      refine ⟨9946945206295777919464181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6631296804197185279642787 9946945206295777919464181)
      ·
        refine ⟨932526113090229179949767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9946945206295777919464181 932526113090229179949767)
        ·
          refine ⟨1398789169635343769924651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932526113090229179949767 1398789169635343769924651)
          ·
            refine ⟨2098183754453015654886977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398789169635343769924651 2098183754453015654886977)
            ·
              refine ⟨1573637815839761741165233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098183754453015654886977 1573637815839761741165233)
              ·
                refine ⟨1180228361879821305873925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1573637815839761741165233 1180228361879821305873925)
                ·
                  refine ⟨221292817852466494851361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1180228361879821305873925 221292817852466494851361)
                  ·
                    rfl

theorem cell20_484837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_484837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484837 prefixEnd_484837 := by exact prefixLift 484837
  have htrace : WordTrace (prefixWord ++ tailWord_484837) baseStart_484837 baseEnd_484837 := by
    simpa [prefixWord, tailWord_484837, baseEnd_484837] using wordTrace_append hprefix tailTrace_484837
  have hstable : (prefixWord ++ tailWord_484837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484837).length < 2 ^ (prefixWord ++ tailWord_484837).sum := by decide
  have hdescent : baseEnd_484837 < baseStart_484837 := by decide
  rcases family_descends (prefixWord ++ tailWord_484837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484871 : List Nat := [1, 1, 4, 3, 2, 2, 3, 2, 2]
def baseStart_484871 : Nat := 118140960795 + 484871 * 2 ^ 59
def prefixEnd_484871 : Nat := 4983230072969 + 3 ^ 40 * 484871 * 2
def baseEnd_484871 : Nat := 221308336378913487717889

theorem tailTrace_484871 : CollatzResearch.WordTrace tailWord_484871 prefixEnd_484871 221308336378913487717889 := by
  unfold tailWord_484871
  simp only [CollatzResearch.WordTrace]
  refine ⟨17684698226402651219118467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11789798817601767479412311 17684698226402651219118467)
  ·
    refine ⟨26527047339603976828677701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17684698226402651219118467 26527047339603976828677701)
    ·
      refine ⟨4973821376175745655377069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26527047339603976828677701 4973821376175745655377069)
      ·
        refine ⟨1865183016065904620766401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4973821376175745655377069 1865183016065904620766401)
        ·
          refine ⟨1398887262049428465574801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1865183016065904620766401 1398887262049428465574801)
          ·
            refine ⟨1049165446537071349181101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1398887262049428465574801 1049165446537071349181101)
            ·
              refine ⟨393437042451401755942913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1049165446537071349181101 393437042451401755942913)
              ·
                refine ⟨295077781838551316957185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393437042451401755942913 295077781838551316957185)
                ·
                  refine ⟨221308336378913487717889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295077781838551316957185 221308336378913487717889)
                  ·
                    rfl

theorem cell20_484871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 2].length) (baseStart_484871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484871 prefixEnd_484871 := by exact prefixLift 484871
  have htrace : WordTrace (prefixWord ++ tailWord_484871) baseStart_484871 baseEnd_484871 := by
    simpa [prefixWord, tailWord_484871, baseEnd_484871] using wordTrace_append hprefix tailTrace_484871
  have hstable : (prefixWord ++ tailWord_484871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484871).length < 2 ^ (prefixWord ++ tailWord_484871).sum := by decide
  have hdescent : baseEnd_484871 < baseStart_484871 := by decide
  rcases family_descends (prefixWord ++ tailWord_484871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484885 : List Nat := [1, 3, 2, 1, 3, 4, 2, 1, 3]
def baseStart_484885 : Nat := 118140960795 + 484885 * 2 ^ 59
def prefixEnd_484885 : Nat := 4983230072969 + 3 ^ 40 * 484885 * 2
def baseEnd_484885 : Nat := 221314726360391661251165

theorem tailTrace_484885 : CollatzResearch.WordTrace tailWord_484885 prefixEnd_484885 221314726360391661251165 := by
  unfold tailWord_484885
  simp only [CollatzResearch.WordTrace]
  refine ⟨17685208848351931610128109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11790139232234621073418739 17685208848351931610128109)
  ·
    refine ⟨6631953318131974353798041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17685208848351931610128109 6631953318131974353798041)
    ·
      refine ⟨4973964988598980765348531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6631953318131974353798041 4973964988598980765348531)
      ·
        refine ⟨7460947482898471148022797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4973964988598980765348531 7460947482898471148022797)
        ·
          refine ⟨2797855306086926680508549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7460947482898471148022797 2797855306086926680508549)
          ·
            refine ⟨524597869891298752595353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2797855306086926680508549 524597869891298752595353)
            ·
              refine ⟨393448402418474064446515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524597869891298752595353 393448402418474064446515)
              ·
                refine ⟨590172603627711096669773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393448402418474064446515 590172603627711096669773)
                ·
                  refine ⟨221314726360391661251165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590172603627711096669773 221314726360391661251165)
                  ·
                    rfl

theorem cell20_484885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_484885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484885 prefixEnd_484885 := by exact prefixLift 484885
  have htrace : WordTrace (prefixWord ++ tailWord_484885) baseStart_484885 baseEnd_484885 := by
    simpa [prefixWord, tailWord_484885, baseEnd_484885] using wordTrace_append hprefix tailTrace_484885
  have hstable : (prefixWord ++ tailWord_484885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484885).length < 2 ^ (prefixWord ++ tailWord_484885).sum := by decide
  have hdescent : baseEnd_484885 < baseStart_484885 := by decide
  rcases family_descends (prefixWord ++ tailWord_484885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484913 : List Nat := [1, 2, 2, 3, 1, 1, 1, 7, 2]
def baseStart_484913 : Nat := 118140960795 + 484913 * 2 ^ 59
def prefixEnd_484913 : Nat := 4983230072969 + 3 ^ 40 * 484913 * 2
def baseEnd_484913 : Nat := 221327506323348008317717

theorem tailTrace_484913 : CollatzResearch.WordTrace tailWord_484913 prefixEnd_484913 221327506323348008317717 := by
  unfold tailWord_484913
  simp only [CollatzResearch.WordTrace]
  refine ⟨17686230092250492392147393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11790820061500328261431595 17686230092250492392147393)
  ·
    refine ⟨13264672569187869294110545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17686230092250492392147393 13264672569187869294110545)
    ·
      refine ⟨9948504426890901970582909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13264672569187869294110545 9948504426890901970582909)
      ·
        refine ⟨3730689160084088238968591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9948504426890901970582909 3730689160084088238968591)
        ·
          refine ⟨5596033740126132358452887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3730689160084088238968591 5596033740126132358452887)
          ·
            refine ⟨8394050610189198537679331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5596033740126132358452887 8394050610189198537679331)
            ·
              refine ⟨12591075915283797806518997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8394050610189198537679331 12591075915283797806518997)
              ·
                refine ⟨295103341764464011090289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12591075915283797806518997 295103341764464011090289)
                ·
                  refine ⟨221327506323348008317717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295103341764464011090289 221327506323348008317717)
                  ·
                    rfl

theorem cell20_484913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 2].length) (baseStart_484913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484913 prefixEnd_484913 := by exact prefixLift 484913
  have htrace : WordTrace (prefixWord ++ tailWord_484913) baseStart_484913 baseEnd_484913 := by
    simpa [prefixWord, tailWord_484913, baseEnd_484913] using wordTrace_append hprefix tailTrace_484913
  have hstable : (prefixWord ++ tailWord_484913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484913).length < 2 ^ (prefixWord ++ tailWord_484913).sum := by decide
  have hdescent : baseEnd_484913 < baseStart_484913 := by decide
  rcases family_descends (prefixWord ++ tailWord_484913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484927 : List Nat := [1, 1, 2, 2, 3, 3, 1, 4, 3]
def baseStart_484927 : Nat := 118140960795 + 484927 * 2 ^ 59
def prefixEnd_484927 : Nat := 4983230072969 + 3 ^ 40 * 484927 * 2
def baseEnd_484927 : Nat := 221333896304826181850993

theorem tailTrace_484927 : CollatzResearch.WordTrace tailWord_484927 prefixEnd_484927 221333896304826181850993 := by
  unfold tailWord_484927
  simp only [CollatzResearch.WordTrace]
  refine ⟨17686740714199772783157035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11791160476133181855438023 17686740714199772783157035)
  ·
    refine ⟨26530111071299659174735553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17686740714199772783157035 26530111071299659174735553)
    ·
      refine ⟨19897583303474744381051665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26530111071299659174735553 19897583303474744381051665)
      ·
        refine ⟨14923187477606058285788749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19897583303474744381051665 14923187477606058285788749)
        ·
          refine ⟨5596195304102271857170781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14923187477606058285788749 5596195304102271857170781)
          ·
            refine ⟨2098573239038351946439043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5596195304102271857170781 2098573239038351946439043)
            ·
              refine ⟨3147859858557527919658565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098573239038351946439043 3147859858557527919658565)
              ·
                refine ⟨590223723479536484935981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3147859858557527919658565 590223723479536484935981)
                ·
                  refine ⟨221333896304826181850993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590223723479536484935981 221333896304826181850993)
                  ·
                    rfl

theorem cell20_484927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 3].length) (baseStart_484927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484927 prefixEnd_484927 := by exact prefixLift 484927
  have htrace : WordTrace (prefixWord ++ tailWord_484927) baseStart_484927 baseEnd_484927 := by
    simpa [prefixWord, tailWord_484927, baseEnd_484927] using wordTrace_append hprefix tailTrace_484927
  have hstable : (prefixWord ++ tailWord_484927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484927).length < 2 ^ (prefixWord ++ tailWord_484927).sum := by decide
  have hdescent : baseEnd_484927 < baseStart_484927 := by decide
  rcases family_descends (prefixWord ++ tailWord_484927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484968 : List Nat := [2, 1, 4, 3, 1, 1, 1, 5, 2]
def baseStart_484968 : Nat := 118140960795 + 484968 * 2 ^ 59
def prefixEnd_484968 : Nat := 4983230072969 + 3 ^ 40 * 484968 * 2
def baseEnd_484968 : Nat := 221352609822012261484159

theorem tailTrace_484968 : CollatzResearch.WordTrace tailWord_484968 prefixEnd_484968 221352609822012261484159 := by
  unfold tailWord_484968
  simp only [CollatzResearch.WordTrace]
  refine ⟨8844118053525618392699779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11792157404700824523599705 8844118053525618392699779)
  ·
    refine ⟨13266177080288427589049669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8844118053525618392699779 13266177080288427589049669)
    ·
      refine ⟨2487408202554080172946813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13266177080288427589049669 2487408202554080172946813)
      ·
        refine ⟨932778075957780064855055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2487408202554080172946813 932778075957780064855055)
        ·
          refine ⟨1399167113936670097282583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932778075957780064855055 1399167113936670097282583)
          ·
            refine ⟨2098750670905005145923875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399167113936670097282583 2098750670905005145923875)
            ·
              refine ⟨3148126006357507718885813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098750670905005145923875 3148126006357507718885813)
              ·
                refine ⟨295136813096016348645545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3148126006357507718885813 295136813096016348645545)
                ·
                  refine ⟨221352609822012261484159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295136813096016348645545 221352609822012261484159)
                  ·
                    rfl

theorem cell20_484968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 2].length) (baseStart_484968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484968 prefixEnd_484968 := by exact prefixLift 484968
  have htrace : WordTrace (prefixWord ++ tailWord_484968) baseStart_484968 baseEnd_484968 := by
    simpa [prefixWord, tailWord_484968, baseEnd_484968] using wordTrace_append hprefix tailTrace_484968
  have hstable : (prefixWord ++ tailWord_484968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484968).length < 2 ^ (prefixWord ++ tailWord_484968).sum := by decide
  have hdescent : baseEnd_484968 < baseStart_484968 := by decide
  rcases family_descends (prefixWord ++ tailWord_484968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484982 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_484982 : Nat := 118140960795 + 484982 * 2 ^ 59
def prefixEnd_484982 : Nat := 4983230072969 + 3 ^ 40 * 484982 * 2
def baseEnd_484982 : Nat := 221358999803490435017435

theorem tailTrace_484982 : CollatzResearch.WordTrace tailWord_484982 prefixEnd_484982 221358999803490435017435 := by
  unfold tailWord_484982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1105546670562532323525575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11792497819333678117606133 1105546670562532323525575)
  ·
    refine ⟨1658320005843798485288363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1105546670562532323525575 1658320005843798485288363)
    ·
      refine ⟨2487480008765697727932545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1658320005843798485288363 2487480008765697727932545)
      ·
        refine ⟨1865610006574273295949409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2487480008765697727932545 1865610006574273295949409)
        ·
          refine ⟨1399207504930704971962057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1865610006574273295949409 1399207504930704971962057)
          ·
            refine ⟨1049405628698028728971543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1399207504930704971962057 1049405628698028728971543)
            ·
              refine ⟨1574108443047043093457315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049405628698028728971543 1574108443047043093457315)
              ·
                refine ⟨2361162664570564640185973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574108443047043093457315 2361162664570564640185973)
                ·
                  refine ⟨221358999803490435017435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2361162664570564640185973 221358999803490435017435)
                  ·
                    rfl

theorem cell20_484982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_484982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484982 prefixEnd_484982 := by exact prefixLift 484982
  have htrace : WordTrace (prefixWord ++ tailWord_484982) baseStart_484982 baseEnd_484982 := by
    simpa [prefixWord, tailWord_484982, baseEnd_484982] using wordTrace_append hprefix tailTrace_484982
  have hstable : (prefixWord ++ tailWord_484982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484982).length < 2 ^ (prefixWord ++ tailWord_484982).sum := by decide
  have hdescent : baseEnd_484982 < baseStart_484982 := by decide
  rcases family_descends (prefixWord ++ tailWord_484982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484989 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 4]
def baseStart_484989 : Nat := 118140960795 + 484989 * 2 ^ 59
def prefixEnd_484989 : Nat := 4983230072969 + 3 ^ 40 * 484989 * 2
def baseEnd_484989 : Nat := 221362194794229521784073

theorem tailTrace_484989 : CollatzResearch.WordTrace tailWord_484989 prefixEnd_484989 221362194794229521784073 := by
  unfold tailWord_484989
  simp only [CollatzResearch.WordTrace]
  refine ⟨17689002039975157371914021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11792668026650104914609347 17689002039975157371914021)
  ·
    refine ⟨3316687882495342007233879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17689002039975157371914021 3316687882495342007233879)
    ·
      refine ⟨4975031823743013010850819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3316687882495342007233879 4975031823743013010850819)
      ·
        refine ⟨7462547735614519516276229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4975031823743013010850819 7462547735614519516276229)
        ·
          refine ⟨1399227700427722409301793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7462547735614519516276229 1399227700427722409301793)
          ·
            refine ⟨1049420775320791806976345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1399227700427722409301793 1049420775320791806976345)
            ·
              refine ⟨787065581490593855232259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1049420775320791806976345 787065581490593855232259)
              ·
                refine ⟨1180598372235890782848389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787065581490593855232259 1180598372235890782848389)
                ·
                  refine ⟨221362194794229521784073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1180598372235890782848389 221362194794229521784073)
                  ·
                    rfl

theorem cell20_484989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_484989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_484989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_484989 prefixEnd_484989 := by exact prefixLift 484989
  have htrace : WordTrace (prefixWord ++ tailWord_484989) baseStart_484989 baseEnd_484989 := by
    simpa [prefixWord, tailWord_484989, baseEnd_484989] using wordTrace_append hprefix tailTrace_484989
  have hstable : (prefixWord ++ tailWord_484989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484989).length < 2 ^ (prefixWord ++ tailWord_484989).sum := by decide
  have hdescent : baseEnd_484989 < baseStart_484989 := by decide
  rcases family_descends (prefixWord ++ tailWord_484989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485055 : List Nat := [1, 1, 2, 2, 2, 3, 4, 5]
def baseStart_485055 : Nat := 118140960795 + 485055 * 2 ^ 59
def prefixEnd_485055 : Nat := 4983230072969 + 3 ^ 40 * 485055 * 2
def baseEnd_485055 : Nat := 73797439664208875194601

theorem tailTrace_485055 : CollatzResearch.WordTrace tailWord_485055 prefixEnd_485055 73797439664208875194601 := by
  unfold tailWord_485055
  simp only [CollatzResearch.WordTrace]
  refine ⟨17691409257736050643816619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11794272838490700429211079 17691409257736050643816619)
  ·
    refine ⟨26537113886604075965724929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17691409257736050643816619 26537113886604075965724929)
    ·
      refine ⟨19902835414953056974293697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26537113886604075965724929 19902835414953056974293697)
      ·
        refine ⟨14927126561214792730720273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19902835414953056974293697 14927126561214792730720273)
        ·
          refine ⟨11195344920911094548040205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14927126561214792730720273 11195344920911094548040205)
          ·
            refine ⟨4198254345341660455515077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11195344920911094548040205 4198254345341660455515077)
            ·
              refine ⟨787172689751561335409077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4198254345341660455515077 787172689751561335409077)
              ·
                refine ⟨73797439664208875194601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 787172689751561335409077 73797439664208875194601)
                ·
                  rfl

theorem cell20_485055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 5].length) (baseStart_485055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485055 prefixEnd_485055 := by exact prefixLift 485055
  have htrace : WordTrace (prefixWord ++ tailWord_485055) baseStart_485055 baseEnd_485055 := by
    simpa [prefixWord, tailWord_485055, baseEnd_485055] using wordTrace_append hprefix tailTrace_485055
  have hstable : (prefixWord ++ tailWord_485055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485055).length < 2 ^ (prefixWord ++ tailWord_485055).sum := by decide
  have hdescent : baseEnd_485055 < baseStart_485055 := by decide
  rcases family_descends (prefixWord ++ tailWord_485055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485095 : List Nat := [1, 1, 5, 4, 2, 1, 2, 2, 2]
def baseStart_485095 : Nat := 118140960795 + 485095 * 2 ^ 59
def prefixEnd_485095 : Nat := 4983230072969 + 3 ^ 40 * 485095 * 2
def baseEnd_485095 : Nat := 221410576082564264250307

theorem tailTrace_485095 : CollatzResearch.WordTrace tailWord_485095 prefixEnd_485095 221410576082564264250307 := by
  unfold tailWord_485095
  simp only [CollatzResearch.WordTrace]
  refine ⟨17692868177591137475272739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11795245451727424983515159 17692868177591137475272739)
  ·
    refine ⟨26539302266386706212909109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17692868177591137475272739 26539302266386706212909109)
    ·
      refine ⟨2488059587473753707460229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26539302266386706212909109 2488059587473753707460229)
      ·
        refine ⟨466511172651328820148793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2488059587473753707460229 466511172651328820148793)
        ·
          refine ⟨349883379488496615111595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466511172651328820148793 349883379488496615111595)
          ·
            refine ⟨524825069232744922667393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349883379488496615111595 524825069232744922667393)
            ·
              refine ⟨393618801924558692000545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524825069232744922667393 393618801924558692000545)
              ·
                refine ⟨295214101443419019000409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393618801924558692000545 295214101443419019000409)
                ·
                  refine ⟨221410576082564264250307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295214101443419019000409 221410576082564264250307)
                  ·
                    rfl

theorem cell20_485095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 2].length) (baseStart_485095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485095 prefixEnd_485095 := by exact prefixLift 485095
  have htrace : WordTrace (prefixWord ++ tailWord_485095) baseStart_485095 baseEnd_485095 := by
    simpa [prefixWord, tailWord_485095, baseEnd_485095] using wordTrace_append hprefix tailTrace_485095
  have hstable : (prefixWord ++ tailWord_485095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485095).length < 2 ^ (prefixWord ++ tailWord_485095).sum := by decide
  have hdescent : baseEnd_485095 < baseStart_485095 := by decide
  rcases family_descends (prefixWord ++ tailWord_485095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485096 : List Nat := [2, 1, 4, 1, 3, 2, 2, 2, 3]
def baseStart_485096 : Nat := 118140960795 + 485096 * 2 ^ 59
def prefixEnd_485096 : Nat := 4983230072969 + 3 ^ 40 * 485096 * 2
def baseEnd_485096 : Nat := 221411032509812705216969

theorem tailTrace_485096 : CollatzResearch.WordTrace tailWord_485096 prefixEnd_485096 221411032509812705216969 := by
  unfold tailWord_485096
  simp only [CollatzResearch.WordTrace]
  refine ⟨8846452325293757323029571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11795269767058343097372761 8846452325293757323029571)
  ·
    refine ⟨13269678487940635984544357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8846452325293757323029571 13269678487940635984544357)
    ·
      refine ⟨2488064716488869247102067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13269678487940635984544357 2488064716488869247102067)
      ·
        refine ⟨3732097074733303870653101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2488064716488869247102067 3732097074733303870653101)
        ·
          refine ⟨1399536403024988951494913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3732097074733303870653101 1399536403024988951494913)
          ·
            refine ⟨1049652302268741713621185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1399536403024988951494913 1049652302268741713621185)
            ·
              refine ⟨787239226701556285215889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1049652302268741713621185 787239226701556285215889)
              ·
                refine ⟨590429420026167213911917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787239226701556285215889 590429420026167213911917)
                ·
                  refine ⟨221411032509812705216969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590429420026167213911917 221411032509812705216969)
                  ·
                    rfl

theorem cell20_485096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_485096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485096 prefixEnd_485096 := by exact prefixLift 485096
  have htrace : WordTrace (prefixWord ++ tailWord_485096) baseStart_485096 baseEnd_485096 := by
    simpa [prefixWord, tailWord_485096, baseEnd_485096] using wordTrace_append hprefix tailTrace_485096
  have hstable : (prefixWord ++ tailWord_485096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485096).length < 2 ^ (prefixWord ++ tailWord_485096).sum := by decide
  have hdescent : baseEnd_485096 < baseStart_485096 := by decide
  rcases family_descends (prefixWord ++ tailWord_485096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485100 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 5]
def baseStart_485100 : Nat := 118140960795 + 485100 * 2 ^ 59
def prefixEnd_485100 : Nat := 4983230072969 + 3 ^ 40 * 485100 * 2
def baseEnd_485100 : Nat := 221412858218806469083619

theorem tailTrace_485100 : CollatzResearch.WordTrace tailWord_485100 prefixEnd_485100 221412858218806469083619 := by
  unfold tailWord_485100
  simp only [CollatzResearch.WordTrace]
  refine ⟨8846525271286511664602377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11795367028382015552803169 8846525271286511664602377)
  ·
    refine ⟨6634893953464883748451783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8846525271286511664602377 6634893953464883748451783)
    ·
      refine ⟨9952340930197325622677675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6634893953464883748451783 9952340930197325622677675)
      ·
        refine ⟨14928511395295988434016513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9952340930197325622677675 14928511395295988434016513)
        ·
          refine ⟨11196383546471991325512385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14928511395295988434016513 11196383546471991325512385)
          ·
            refine ⟨8397287659853993494134289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11196383546471991325512385 8397287659853993494134289)
            ·
              refine ⟨6297965744890495120600717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8397287659853993494134289 6297965744890495120600717)
              ·
                refine ⟨2361737154333935670225269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6297965744890495120600717 2361737154333935670225269)
                ·
                  refine ⟨221412858218806469083619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2361737154333935670225269 221412858218806469083619)
                  ·
                    rfl

theorem cell20_485100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_485100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485100 prefixEnd_485100 := by exact prefixLift 485100
  have htrace : WordTrace (prefixWord ++ tailWord_485100) baseStart_485100 baseEnd_485100 := by
    simpa [prefixWord, tailWord_485100, baseEnd_485100] using wordTrace_append hprefix tailTrace_485100
  have hstable : (prefixWord ++ tailWord_485100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485100).length < 2 ^ (prefixWord ++ tailWord_485100).sum := by decide
  have hdescent : baseEnd_485100 < baseStart_485100 := by decide
  rcases family_descends (prefixWord ++ tailWord_485100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485103 : List Nat := [1, 1, 2, 1, 5, 1, 3, 4, 2]
def baseStart_485103 : Nat := 118140960795 + 485103 * 2 ^ 59
def prefixEnd_485103 : Nat := 4983230072969 + 3 ^ 40 * 485103 * 2
def baseEnd_485103 : Nat := 221414227500551791983607

theorem tailTrace_485103 : CollatzResearch.WordTrace tailWord_485103 prefixEnd_485103 221414227500551791983607 := by
  unfold tailWord_485103
  simp only [CollatzResearch.WordTrace]
  refine ⟨17693159961562154841563963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11795439974374769894375975 17693159961562154841563963)
  ·
    refine ⟨26539739942343232262345945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17693159961562154841563963 26539739942343232262345945)
    ·
      refine ⟨19904804956757424196759459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26539739942343232262345945 19904804956757424196759459)
      ·
        refine ⟨29857207435136136295139189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19904804956757424196759459 29857207435136136295139189)
        ·
          refine ⟨2799113197044012777669299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29857207435136136295139189 2799113197044012777669299)
          ·
            refine ⟨4198669795566019166503949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799113197044012777669299 4198669795566019166503949)
            ·
              refine ⟨1574501173337257187438981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4198669795566019166503949 1574501173337257187438981)
              ·
                refine ⟨295218970000735722644809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1574501173337257187438981 295218970000735722644809)
                ·
                  refine ⟨221414227500551791983607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295218970000735722644809 221414227500551791983607)
                  ·
                    rfl

theorem cell20_485103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 2].length) (baseStart_485103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485103 prefixEnd_485103 := by exact prefixLift 485103
  have htrace : WordTrace (prefixWord ++ tailWord_485103) baseStart_485103 baseEnd_485103 := by
    simpa [prefixWord, tailWord_485103, baseEnd_485103] using wordTrace_append hprefix tailTrace_485103
  have hstable : (prefixWord ++ tailWord_485103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485103).length < 2 ^ (prefixWord ++ tailWord_485103).sum := by decide
  have hdescent : baseEnd_485103 < baseStart_485103 := by decide
  rcases family_descends (prefixWord ++ tailWord_485103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485110 : List Nat := [5, 1, 1, 1, 1, 3, 3, 5]
def baseStart_485110 : Nat := 118140960795 + 485110 * 2 ^ 59
def prefixEnd_485110 : Nat := 4983230072969 + 3 ^ 40 * 485110 * 2
def baseEnd_485110 : Nat := 73805807497096959583415

theorem tailTrace_485110 : CollatzResearch.WordTrace tailWord_485110 prefixEnd_485110 73805807497096959583415 := by
  unfold tailWord_485110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1105838454533549689816799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11795610181691196691379189 1105838454533549689816799)
  ·
    refine ⟨1658757681800324534725199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1105838454533549689816799 1658757681800324534725199)
    ·
      refine ⟨2488136522700486802087799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1658757681800324534725199 2488136522700486802087799)
      ·
        refine ⟨3732204784050730203131699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2488136522700486802087799 3732204784050730203131699)
        ·
          refine ⟨5598307176076095304697549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732204784050730203131699 5598307176076095304697549)
          ·
            refine ⟨2099365191028535739261581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5598307176076095304697549 2099365191028535739261581)
            ·
              refine ⟨787261946635700902223093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2099365191028535739261581 787261946635700902223093)
              ·
                refine ⟨73805807497096959583415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 787261946635700902223093 73805807497096959583415)
                ·
                  rfl

theorem cell20_485110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_485110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485110 prefixEnd_485110 := by exact prefixLift 485110
  have htrace : WordTrace (prefixWord ++ tailWord_485110) baseStart_485110 baseEnd_485110 := by
    simpa [prefixWord, tailWord_485110, baseEnd_485110] using wordTrace_append hprefix tailTrace_485110
  have hstable : (prefixWord ++ tailWord_485110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485110).length < 2 ^ (prefixWord ++ tailWord_485110).sum := by decide
  have hdescent : baseEnd_485110 < baseStart_485110 := by decide
  rcases family_descends (prefixWord ++ tailWord_485110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485124 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 6]
def baseStart_485124 : Nat := 118140960795 + 485124 * 2 ^ 59
def prefixEnd_485124 : Nat := 4983230072969 + 3 ^ 40 * 485124 * 2
def baseEnd_485124 : Nat := 221423812472769052283521

theorem tailTrace_485124 : CollatzResearch.WordTrace tailWord_485124 prefixEnd_485124 221423812472769052283521 := by
  unfold tailWord_485124
  simp only [CollatzResearch.WordTrace]
  refine ⟨8846962947243037714039213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11795950596324050285385617 8846962947243037714039213)
  ·
    refine ⟨3317611105216139142764705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8846962947243037714039213 3317611105216139142764705)
    ·
      refine ⟨2488208328912104357073529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3317611105216139142764705 2488208328912104357073529)
      ·
        refine ⟨1866156246684078267805147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2488208328912104357073529 1866156246684078267805147)
        ·
          refine ⟨2799234370026117401707721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1866156246684078267805147 2799234370026117401707721)
          ·
            refine ⟨2099425777519588051280791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2799234370026117401707721 2099425777519588051280791)
            ·
              refine ⟨3149138666279382076921187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2099425777519588051280791 3149138666279382076921187)
              ·
                refine ⟨4723707999419073115381781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3149138666279382076921187 4723707999419073115381781)
                ·
                  refine ⟨221423812472769052283521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4723707999419073115381781 221423812472769052283521)
                  ·
                    rfl

theorem cell20_485124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_485124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485124 prefixEnd_485124 := by exact prefixLift 485124
  have htrace : WordTrace (prefixWord ++ tailWord_485124) baseStart_485124 baseEnd_485124 := by
    simpa [prefixWord, tailWord_485124, baseEnd_485124] using wordTrace_append hprefix tailTrace_485124
  have hstable : (prefixWord ++ tailWord_485124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485124).length < 2 ^ (prefixWord ++ tailWord_485124).sum := by decide
  have hdescent : baseEnd_485124 < baseStart_485124 := by decide
  rcases family_descends (prefixWord ++ tailWord_485124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485127 : List Nat := [1, 1, 4, 4, 2, 1, 3, 4]
def baseStart_485127 : Nat := 118140960795 + 485127 * 2 ^ 59
def prefixEnd_485127 : Nat := 4983230072969 + 3 ^ 40 * 485127 * 2
def baseEnd_485127 : Nat := 73808393918171458394503

theorem tailTrace_485127 : CollatzResearch.WordTrace tailWord_485127 prefixEnd_485127 73808393918171458394503 := by
  unfold tailWord_485127
  simp only [CollatzResearch.WordTrace]
  refine ⟨17694035313475206940437635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11796023542316804626958423 17694035313475206940437635)
  ·
    refine ⟨26541052970212810410656453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17694035313475206940437635 26541052970212810410656453)
    ·
      refine ⟨4976447431914901951998085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26541052970212810410656453 4976447431914901951998085)
      ·
        refine ⟨933083893484044115999641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4976447431914901951998085 933083893484044115999641)
        ·
          refine ⟨699812920113033086999731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 933083893484044115999641 699812920113033086999731)
          ·
            refine ⟨1049719380169549630499597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699812920113033086999731 1049719380169549630499597)
            ·
              refine ⟨393644767563581111437349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1049719380169549630499597 393644767563581111437349)
              ·
                refine ⟨73808393918171458394503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 393644767563581111437349 73808393918171458394503)
                ·
                  rfl

theorem cell20_485127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 4].length) (baseStart_485127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485127 prefixEnd_485127 := by exact prefixLift 485127
  have htrace : WordTrace (prefixWord ++ tailWord_485127) baseStart_485127 baseEnd_485127 := by
    simpa [prefixWord, tailWord_485127, baseEnd_485127] using wordTrace_append hprefix tailTrace_485127
  have hstable : (prefixWord ++ tailWord_485127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485127).length < 2 ^ (prefixWord ++ tailWord_485127).sum := by decide
  have hdescent : baseEnd_485127 < baseStart_485127 := by decide
  rcases family_descends (prefixWord ++ tailWord_485127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485141 : List Nat := [1, 3, 2, 1, 2, 3, 1, 5, 2]
def baseStart_485141 : Nat := 118140960795 + 485141 * 2 ^ 59
def prefixEnd_485141 : Nat := 4983230072969 + 3 ^ 40 * 485141 * 2
def baseEnd_485141 : Nat := 221431571735992548716785

theorem tailTrace_485141 : CollatzResearch.WordTrace tailWord_485141 prefixEnd_485141 221431571735992548716785 := by
  unfold tailWord_485141
  simp only [CollatzResearch.WordTrace]
  refine ⟨17694545935424487331447277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11796363956949658220964851 17694545935424487331447277)
  ·
    refine ⟨6635454725784182749292729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17694545935424487331447277 6635454725784182749292729)
    ·
      refine ⟨4976591044338137061969547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6635454725784182749292729 4976591044338137061969547)
      ·
        refine ⟨7464886566507205592954321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4976591044338137061969547 7464886566507205592954321)
        ·
          refine ⟨5598664924880404194715741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7464886566507205592954321 5598664924880404194715741)
          ·
            refine ⟨2099499346830151573018403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5598664924880404194715741 2099499346830151573018403)
            ·
              refine ⟨3149249020245227359527605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2099499346830151573018403 3149249020245227359527605)
              ·
                refine ⟨295242095647990064955713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3149249020245227359527605 295242095647990064955713)
                ·
                  refine ⟨221431571735992548716785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295242095647990064955713 221431571735992548716785)
                  ·
                    rfl

theorem cell20_485141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_485141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485141 prefixEnd_485141 := by exact prefixLift 485141
  have htrace : WordTrace (prefixWord ++ tailWord_485141) baseStart_485141 baseEnd_485141 := by
    simpa [prefixWord, tailWord_485141, baseEnd_485141] using wordTrace_append hprefix tailTrace_485141
  have hstable : (prefixWord ++ tailWord_485141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485141).length < 2 ^ (prefixWord ++ tailWord_485141).sum := by decide
  have hdescent : baseEnd_485141 < baseStart_485141 := by decide
  rcases family_descends (prefixWord ++ tailWord_485141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485155 : List Nat := [1, 1, 1, 4, 2, 1, 5, 2, 3]
def baseStart_485155 : Nat := 118140960795 + 485155 * 2 ^ 59
def prefixEnd_485155 : Nat := 4983230072969 + 3 ^ 40 * 485155 * 2
def baseEnd_485155 : Nat := 221437961717470722250061

theorem tailTrace_485155 : CollatzResearch.WordTrace tailWord_485155 prefixEnd_485155 221437961717470722250061 := by
  unfold tailWord_485155
  simp only [CollatzResearch.WordTrace]
  refine ⟨17695056557373767722456919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11796704371582511814971279 17695056557373767722456919)
  ·
    refine ⟨26542584836060651583685379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17695056557373767722456919 26542584836060651583685379)
    ·
      refine ⟨39813877254090977375528069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26542584836060651583685379 39813877254090977375528069)
      ·
        refine ⟨7465101985142058257911513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39813877254090977375528069 7465101985142058257911513)
        ·
          refine ⟨5598826488856543693433635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7465101985142058257911513 5598826488856543693433635)
          ·
            refine ⟨8398239733284815540150453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5598826488856543693433635 8398239733284815540150453)
            ·
              refine ⟨787334974995451456889105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8398239733284815540150453 787334974995451456889105)
              ·
                refine ⟨590501231246588592666829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787334974995451456889105 590501231246588592666829)
                ·
                  refine ⟨221437961717470722250061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590501231246588592666829 221437961717470722250061)
                  ·
                    rfl

theorem cell20_485155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 3].length) (baseStart_485155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485155 prefixEnd_485155 := by exact prefixLift 485155
  have htrace : WordTrace (prefixWord ++ tailWord_485155) baseStart_485155 baseEnd_485155 := by
    simpa [prefixWord, tailWord_485155, baseEnd_485155] using wordTrace_append hprefix tailTrace_485155
  have hstable : (prefixWord ++ tailWord_485155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485155).length < 2 ^ (prefixWord ++ tailWord_485155).sum := by decide
  have hdescent : baseEnd_485155 < baseStart_485155 := by decide
  rcases family_descends (prefixWord ++ tailWord_485155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485252 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 7]
def baseStart_485252 : Nat := 118140960795 + 485252 * 2 ^ 59
def prefixEnd_485252 : Nat := 4983230072969 + 3 ^ 40 * 485252 * 2
def baseEnd_485252 : Nat := 221482235160569496016331

theorem tailTrace_485252 : CollatzResearch.WordTrace tailWord_485252 prefixEnd_485252 221482235160569496016331 := by
  unfold tailWord_485252
  simp only [CollatzResearch.WordTrace]
  refine ⟨8849297219011176644369005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11799062958681568859158673 8849297219011176644369005)
  ·
    refine ⟨3318486457129191241638377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8849297219011176644369005 3318486457129191241638377)
    ·
      refine ⟨2488864842846893431228783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3318486457129191241638377 2488864842846893431228783)
      ·
        refine ⟨3733297264270340146843175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2488864842846893431228783 3733297264270340146843175)
        ·
          refine ⟨5599945896405510220264763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3733297264270340146843175 5599945896405510220264763)
          ·
            refine ⟨8399918844608265330397145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5599945896405510220264763 8399918844608265330397145)
            ·
              refine ⟨6299939133456198997797859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8399918844608265330397145 6299939133456198997797859)
              ·
                refine ⟨9449908700184298496696789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6299939133456198997797859 9449908700184298496696789)
                ·
                  refine ⟨221482235160569496016331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9449908700184298496696789 221482235160569496016331)
                  ·
                    rfl

theorem cell20_485252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_485252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485252 prefixEnd_485252 := by exact prefixLift 485252
  have htrace : WordTrace (prefixWord ++ tailWord_485252) baseStart_485252 baseEnd_485252 := by
    simpa [prefixWord, tailWord_485252, baseEnd_485252] using wordTrace_append hprefix tailTrace_485252
  have hstable : (prefixWord ++ tailWord_485252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485252).length < 2 ^ (prefixWord ++ tailWord_485252).sum := by decide
  have hdescent : baseEnd_485252 < baseStart_485252 := by decide
  rcases family_descends (prefixWord ++ tailWord_485252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485262 : List Nat := [4, 1, 1, 5, 1, 8]
def baseStart_485262 : Nat := 118140960795 + 485262 * 2 ^ 59
def prefixEnd_485262 : Nat := 4983230072969 + 3 ^ 40 * 485262 * 2
def baseEnd_485262 : Nat := 8203214793816811321591

theorem tailTrace_485262 : CollatzResearch.WordTrace tailWord_485262 prefixEnd_485262 8203214793816811321591 := by
  unfold tailWord_485262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2212369895998265624575255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11799306111990749997734693 2212369895998265624575255)
  ·
    refine ⟨3318554843997398436862883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2212369895998265624575255 3318554843997398436862883)
    ·
      refine ⟨4977832265996097655294325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3318554843997398436862883 4977832265996097655294325)
      ·
        refine ⟨466671774937134155183843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4977832265996097655294325 466671774937134155183843)
        ·
          refine ⟨700007662405701232775765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466671774937134155183843 700007662405701232775765)
          ·
            refine ⟨8203214793816811321591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 700007662405701232775765 8203214793816811321591)
            ·
              rfl

theorem cell20_485262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 8].length) (baseStart_485262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485262 prefixEnd_485262 := by exact prefixLift 485262
  have htrace : WordTrace (prefixWord ++ tailWord_485262) baseStart_485262 baseEnd_485262 := by
    simpa [prefixWord, tailWord_485262, baseEnd_485262] using wordTrace_append hprefix tailTrace_485262
  have hstable : (prefixWord ++ tailWord_485262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485262).length < 2 ^ (prefixWord ++ tailWord_485262).sum := by decide
  have hdescent : baseEnd_485262 < baseStart_485262 := by decide
  rcases family_descends (prefixWord ++ tailWord_485262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485269 : List Nat := [1, 3, 2, 1, 1, 3, 4, 2, 3]
def baseStart_485269 : Nat := 118140960795 + 485269 * 2 ^ 59
def prefixEnd_485269 : Nat := 4983230072969 + 3 ^ 40 * 485269 * 2
def baseEnd_485269 : Nat := 221489994423792992449595

theorem tailTrace_485269 : CollatzResearch.WordTrace tailWord_485269 prefixEnd_485269 221489994423792992449595 := by
  unfold tailWord_485269
  simp only [CollatzResearch.WordTrace]
  refine ⟨17699214478960765192106861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11799476319307176794737907 17699214478960765192106861)
  ·
    refine ⟨6637205429610286947040073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17699214478960765192106861 6637205429610286947040073)
    ·
      refine ⟨4977904072207715210280055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6637205429610286947040073 4977904072207715210280055)
      ·
        refine ⟨7466856108311572815420083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4977904072207715210280055 7466856108311572815420083)
        ·
          refine ⟨11200284162467359223130125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7466856108311572815420083 11200284162467359223130125)
          ·
            refine ⟨4200106560925259708673797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11200284162467359223130125 4200106560925259708673797)
            ·
              refine ⟨787519980173486195376337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4200106560925259708673797 787519980173486195376337)
              ·
                refine ⟨590639985130114646532253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787519980173486195376337 590639985130114646532253)
                ·
                  refine ⟨221489994423792992449595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590639985130114646532253 221489994423792992449595)
                  ·
                    rfl

theorem cell20_485269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_485269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485269 prefixEnd_485269 := by exact prefixLift 485269
  have htrace : WordTrace (prefixWord ++ tailWord_485269) baseStart_485269 baseEnd_485269 := by
    simpa [prefixWord, tailWord_485269, baseEnd_485269] using wordTrace_append hprefix tailTrace_485269
  have hstable : (prefixWord ++ tailWord_485269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485269).length < 2 ^ (prefixWord ++ tailWord_485269).sum := by decide
  have hdescent : baseEnd_485269 < baseStart_485269 := by decide
  rcases family_descends (prefixWord ++ tailWord_485269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485279 : List Nat := [1, 1, 2, 5, 4, 1, 1, 5]
def baseStart_485279 : Nat := 118140960795 + 485279 * 2 ^ 59
def prefixEnd_485279 : Nat := 4983230072969 + 3 ^ 40 * 485279 * 2
def baseEnd_485279 : Nat := 73831519565425800705407

theorem tailTrace_485279 : CollatzResearch.WordTrace tailWord_485279 prefixEnd_485279 73831519565425800705407 := by
  unfold tailWord_485279
  simp only [CollatzResearch.WordTrace]
  refine ⟨17699579208924536899970891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11799719472616357933313927 17699579208924536899970891)
  ·
    refine ⟨26549368813386805349956337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17699579208924536899970891 26549368813386805349956337)
    ·
      refine ⟨19912026610040104012467253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26549368813386805349956337 19912026610040104012467253)
      ·
        refine ⟨1866752494691259751168805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19912026610040104012467253 1866752494691259751168805)
        ·
          refine ⟨350016092754611203344151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1866752494691259751168805 350016092754611203344151)
          ·
            refine ⟨525024139131916805016227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350016092754611203344151 525024139131916805016227)
            ·
              refine ⟨787536208697875207524341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525024139131916805016227 787536208697875207524341)
              ·
                refine ⟨73831519565425800705407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 787536208697875207524341 73831519565425800705407)
                ·
                  rfl

theorem cell20_485279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 5].length) (baseStart_485279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485279 prefixEnd_485279 := by exact prefixLift 485279
  have htrace : WordTrace (prefixWord ++ tailWord_485279) baseStart_485279 baseEnd_485279 := by
    simpa [prefixWord, tailWord_485279, baseEnd_485279] using wordTrace_append hprefix tailTrace_485279
  have hstable : (prefixWord ++ tailWord_485279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485279).length < 2 ^ (prefixWord ++ tailWord_485279).sum := by decide
  have hdescent : baseEnd_485279 < baseStart_485279 := by decide
  rcases family_descends (prefixWord ++ tailWord_485279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485310 : List Nat := [4, 2, 1, 1, 1, 4, 2, 3, 2]
def baseStart_485310 : Nat := 118140960795 + 485310 * 2 ^ 59
def prefixEnd_485310 : Nat := 4983230072969 + 3 ^ 40 * 485310 * 2
def baseEnd_485310 : Nat := 221508707940979072082761

theorem tailTrace_485310 : CollatzResearch.WordTrace tailWord_485310 prefixEnd_485310 221508707940979072082761 := by
  unfold tailWord_485310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2212588733976528649293673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11800473247874819462899589 2212588733976528649293673)
  ·
    refine ⟨1659441550482396486970255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2212588733976528649293673 1659441550482396486970255)
    ·
      refine ⟨2489162325723594730455383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1659441550482396486970255 2489162325723594730455383)
      ·
        refine ⟨3733743488585392095683075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2489162325723594730455383 3733743488585392095683075)
        ·
          refine ⟨5600615232878088143524613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3733743488585392095683075 5600615232878088143524613)
          ·
            refine ⟨1050115356164641526910865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5600615232878088143524613 1050115356164641526910865)
            ·
              refine ⟨787586517123481145183149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1050115356164641526910865 787586517123481145183149)
              ·
                refine ⟨295344943921305429443681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 787586517123481145183149 295344943921305429443681)
                ·
                  refine ⟨221508707940979072082761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295344943921305429443681 221508707940979072082761)
                  ·
                    rfl

theorem cell20_485310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_485310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485310 prefixEnd_485310 := by exact prefixLift 485310
  have htrace : WordTrace (prefixWord ++ tailWord_485310) baseStart_485310 baseEnd_485310 := by
    simpa [prefixWord, tailWord_485310, baseEnd_485310] using wordTrace_append hprefix tailTrace_485310
  have hstable : (prefixWord ++ tailWord_485310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485310).length < 2 ^ (prefixWord ++ tailWord_485310).sum := by decide
  have hdescent : baseEnd_485310 < baseStart_485310 := by decide
  rcases family_descends (prefixWord ++ tailWord_485310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485324 : List Nat := [2, 2, 1, 4, 1, 4, 1, 2, 3]
def baseStart_485324 : Nat := 118140960795 + 485324 * 2 ^ 59
def prefixEnd_485324 : Nat := 4983230072969 + 3 ^ 40 * 485324 * 2
def baseEnd_485324 : Nat := 221515097922457245616037

theorem tailTrace_485324 : CollatzResearch.WordTrace tailWord_485324 prefixEnd_485324 221515097922457245616037 := by
  unfold tailWord_485324
  simp only [CollatzResearch.WordTrace]
  refine ⟨8850610246880754792679513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11800813662507673056906017 8850610246880754792679513)
  ·
    refine ⟨6637957685160566094509635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8850610246880754792679513 6637957685160566094509635)
    ·
      refine ⟨9956936527740849141764453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6637957685160566094509635 9956936527740849141764453)
      ·
        refine ⟨1866925598951409214080835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9956936527740849141764453 1866925598951409214080835)
        ·
          refine ⟨2800388398427113821121253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1866925598951409214080835 2800388398427113821121253)
          ·
            refine ⟨525072824705083841460235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2800388398427113821121253 525072824705083841460235)
            ·
              refine ⟨787609237057625762190353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525072824705083841460235 787609237057625762190353)
              ·
                refine ⟨590706927793219321642765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787609237057625762190353 590706927793219321642765)
                ·
                  refine ⟨221515097922457245616037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590706927793219321642765 221515097922457245616037)
                  ·
                    rfl

theorem cell20_485324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_485324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485324 prefixEnd_485324 := by exact prefixLift 485324
  have htrace : WordTrace (prefixWord ++ tailWord_485324) baseStart_485324 baseEnd_485324 := by
    simpa [prefixWord, tailWord_485324, baseEnd_485324] using wordTrace_append hprefix tailTrace_485324
  have hstable : (prefixWord ++ tailWord_485324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485324).length < 2 ^ (prefixWord ++ tailWord_485324).sum := by decide
  have hdescent : baseEnd_485324 < baseStart_485324 := by decide
  rcases family_descends (prefixWord ++ tailWord_485324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485341 : List Nat := [1, 4, 3, 1, 3, 1, 3, 1, 3]
def baseStart_485341 : Nat := 118140960795 + 485341 * 2 ^ 59
def prefixEnd_485341 : Nat := 4983230072969 + 3 ^ 40 * 485341 * 2
def baseEnd_485341 : Nat := 221522857185680742049301

theorem tailTrace_485341 : CollatzResearch.WordTrace tailWord_485341 prefixEnd_485341 221522857185680742049301 := by
  unfold tailWord_485341
  simp only [CollatzResearch.WordTrace]
  refine ⟨17701840534699921488727877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11801227023133280992485251 17701840534699921488727877)
  ·
    refine ⟨3319095100256235279136477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17701840534699921488727877 3319095100256235279136477)
    ·
      refine ⟨1244660662596088229676179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3319095100256235279136477 1244660662596088229676179)
      ·
        refine ⟨1866990993894132344514269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244660662596088229676179 1866990993894132344514269)
        ·
          refine ⟨700121622710299629192851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1866990993894132344514269 700121622710299629192851)
          ·
            refine ⟨1050182434065449443789277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700121622710299629192851 1050182434065449443789277)
            ·
              refine ⟨393818412774543541420979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1050182434065449443789277 393818412774543541420979)
              ·
                refine ⟨590727619161815312131469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393818412774543541420979 590727619161815312131469)
                ·
                  refine ⟨221522857185680742049301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590727619161815312131469 221522857185680742049301)
                  ·
                    rfl

theorem cell20_485341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_485341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485341 prefixEnd_485341 := by exact prefixLift 485341
  have htrace : WordTrace (prefixWord ++ tailWord_485341) baseStart_485341 baseEnd_485341 := by
    simpa [prefixWord, tailWord_485341, baseEnd_485341] using wordTrace_append hprefix tailTrace_485341
  have hstable : (prefixWord ++ tailWord_485341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485341).length < 2 ^ (prefixWord ++ tailWord_485341).sum := by decide
  have hdescent : baseEnd_485341 < baseStart_485341 := by decide
  rcases family_descends (prefixWord ++ tailWord_485341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485369 : List Nat := [1, 2, 1, 3, 1, 4, 3, 3, 2]
def baseStart_485369 : Nat := 118140960795 + 485369 * 2 ^ 59
def prefixEnd_485369 : Nat := 4983230072969 + 3 ^ 40 * 485369 * 2
def baseEnd_485369 : Nat := 221535637148637089115853

theorem tailTrace_485369 : CollatzResearch.WordTrace tailWord_485369 prefixEnd_485369 221535637148637089115853 := by
  unfold tailWord_485369
  simp only [CollatzResearch.WordTrace]
  refine ⟨17702861778598482270747161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11801907852398988180498107 17702861778598482270747161)
  ·
    refine ⟨13277146333948861703060371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17702861778598482270747161 13277146333948861703060371)
    ·
      refine ⟨19915719500923292554590557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13277146333948861703060371 19915719500923292554590557)
      ·
        refine ⟨7468394812846234707971459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19915719500923292554590557 7468394812846234707971459)
        ·
          refine ⟨11202592219269352061957189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7468394812846234707971459 11202592219269352061957189)
          ·
            refine ⟨2100486041113003511616973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11202592219269352061957189 2100486041113003511616973)
            ·
              refine ⟨787682265417376316856365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2100486041113003511616973 787682265417376316856365)
              ·
                refine ⟨295380849531516118821137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 787682265417376316856365 295380849531516118821137)
                ·
                  refine ⟨221535637148637089115853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295380849531516118821137 221535637148637089115853)
                  ·
                    rfl

theorem cell20_485369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 2].length) (baseStart_485369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485369 prefixEnd_485369 := by exact prefixLift 485369
  have htrace : WordTrace (prefixWord ++ tailWord_485369) baseStart_485369 baseEnd_485369 := by
    simpa [prefixWord, tailWord_485369, baseEnd_485369] using wordTrace_append hprefix tailTrace_485369
  have hstable : (prefixWord ++ tailWord_485369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485369).length < 2 ^ (prefixWord ++ tailWord_485369).sum := by decide
  have hdescent : baseEnd_485369 < baseStart_485369 := by decide
  rcases family_descends (prefixWord ++ tailWord_485369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485373 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 6]
def baseStart_485373 : Nat := 118140960795 + 485373 * 2 ^ 59
def prefixEnd_485373 : Nat := 4983230072969 + 3 ^ 40 * 485373 * 2
def baseEnd_485373 : Nat := 221537462857630852982503

theorem tailTrace_485373 : CollatzResearch.WordTrace tailWord_485373 prefixEnd_485373 221537462857630852982503 := by
  unfold tailWord_485373
  simp only [CollatzResearch.WordTrace]
  refine ⟨17703007670583990953892773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11802005113722660635928515 17703007670583990953892773)
  ·
    refine ⟨3319313938234498303854895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17703007670583990953892773 3319313938234498303854895)
    ·
      refine ⟨4978970907351747455782343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3319313938234498303854895 4978970907351747455782343)
      ·
        refine ⟨7468456361027621183673515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4978970907351747455782343 7468456361027621183673515)
        ·
          refine ⟨11202684541541431775510273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7468456361027621183673515 11202684541541431775510273)
          ·
            refine ⟨8402013406156073831632705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11202684541541431775510273 8402013406156073831632705)
            ·
              refine ⟨6301510054617055373724529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8402013406156073831632705 6301510054617055373724529)
              ·
                refine ⟨4726132540962791530293397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6301510054617055373724529 4726132540962791530293397)
                ·
                  refine ⟨221537462857630852982503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4726132540962791530293397 221537462857630852982503)
                  ·
                    rfl

theorem cell20_485373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_485373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485373 prefixEnd_485373 := by exact prefixLift 485373
  have htrace : WordTrace (prefixWord ++ tailWord_485373) baseStart_485373 baseEnd_485373 := by
    simpa [prefixWord, tailWord_485373, baseEnd_485373] using wordTrace_append hprefix tailTrace_485373
  have hstable : (prefixWord ++ tailWord_485373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485373).length < 2 ^ (prefixWord ++ tailWord_485373).sum := by decide
  have hdescent : baseEnd_485373 < baseStart_485373 := by decide
  rcases family_descends (prefixWord ++ tailWord_485373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485386 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 4]
def baseStart_485386 : Nat := 118140960795 + 485386 * 2 ^ 59
def prefixEnd_485386 : Nat := 4983230072969 + 3 ^ 40 * 485386 * 2
def baseEnd_485386 : Nat := 221543396411860585549117

theorem tailTrace_485386 : CollatzResearch.WordTrace tailWord_485386 prefixEnd_485386 221543396411860585549117 := by
  unfold tailWord_485386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4425870454884223543529003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11802321213024596116077341 4425870454884223543529003)
  ·
    refine ⟨6638805682326335315293505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4425870454884223543529003 6638805682326335315293505)
    ·
      refine ⟨4979104261744751486470129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6638805682326335315293505 4979104261744751486470129)
      ·
        refine ⟨3734328196308563614852597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4979104261744751486470129 3734328196308563614852597)
        ·
          refine ⟨350093268403927838892431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3734328196308563614852597 350093268403927838892431)
          ·
            refine ⟨525139902605891758338647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350093268403927838892431 525139902605891758338647)
            ·
              refine ⟨787709853908837637507971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525139902605891758338647 787709853908837637507971)
              ·
                refine ⟨1181564780863256456261957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787709853908837637507971 1181564780863256456261957)
                ·
                  refine ⟨221543396411860585549117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1181564780863256456261957 221543396411860585549117)
                  ·
                    rfl

theorem cell20_485386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_485386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485386 prefixEnd_485386 := by exact prefixLift 485386
  have htrace : WordTrace (prefixWord ++ tailWord_485386) baseStart_485386 baseEnd_485386 := by
    simpa [prefixWord, tailWord_485386, baseEnd_485386] using wordTrace_append hprefix tailTrace_485386
  have hstable : (prefixWord ++ tailWord_485386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485386).length < 2 ^ (prefixWord ++ tailWord_485386).sum := by decide
  have hdescent : baseEnd_485386 < baseStart_485386 := by decide
  rcases family_descends (prefixWord ++ tailWord_485386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485411 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 6]
def baseStart_485411 : Nat := 118140960795 + 485411 * 2 ^ 59
def prefixEnd_485411 : Nat := 4983230072969 + 3 ^ 40 * 485411 * 2
def baseEnd_485411 : Nat := 221554807093071609715681

theorem tailTrace_485411 : CollatzResearch.WordTrace tailWord_485411 prefixEnd_485411 221554807093071609715681 := by
  unfold tailWord_485411
  simp only [CollatzResearch.WordTrace]
  refine ⟨17704393644446323443776087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11802929096297548962517391 17704393644446323443776087)
  ·
    refine ⟨26556590466669485165664131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17704393644446323443776087 26556590466669485165664131)
    ·
      refine ⟨39834885700004227748496197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26556590466669485165664131 39834885700004227748496197)
      ·
        refine ⟨7469041068750792702843037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39834885700004227748496197 7469041068750792702843037)
        ·
          refine ⟨2800890400781547263566139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7469041068750792702843037 2800890400781547263566139)
          ·
            refine ⟨4201335601172320895349209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2800890400781547263566139 4201335601172320895349209)
            ·
              refine ⟨3151001700879240671511907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4201335601172320895349209 3151001700879240671511907)
              ·
                refine ⟨4726502551318861007267861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3151001700879240671511907 4726502551318861007267861)
                ·
                  refine ⟨221554807093071609715681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4726502551318861007267861 221554807093071609715681)
                  ·
                    rfl

theorem cell20_485411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_485411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485411 prefixEnd_485411 := by exact prefixLift 485411
  have htrace : WordTrace (prefixWord ++ tailWord_485411) baseStart_485411 baseEnd_485411 := by
    simpa [prefixWord, tailWord_485411, baseEnd_485411] using wordTrace_append hprefix tailTrace_485411
  have hstable : (prefixWord ++ tailWord_485411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485411).length < 2 ^ (prefixWord ++ tailWord_485411).sum := by decide
  have hdescent : baseEnd_485411 < baseStart_485411 := by decide
  rcases family_descends (prefixWord ++ tailWord_485411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485441 : List Nat := [1, 2, 5, 1, 2, 3, 2, 2, 2]
def baseStart_485441 : Nat := 118140960795 + 485441 * 2 ^ 59
def prefixEnd_485441 : Nat := 4983230072969 + 3 ^ 40 * 485441 * 2
def baseEnd_485441 : Nat := 221568499910524838715559

theorem tailTrace_485441 : CollatzResearch.WordTrace tailWord_485441 prefixEnd_485441 221568499910524838715559 := by
  unfold tailWord_485441
  simp only [CollatzResearch.WordTrace]
  refine ⟨17705487834337638567368177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11803658556225092378245451 17705487834337638567368177)
  ·
    refine ⟨13279115875753228925526133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17705487834337638567368177 13279115875753228925526133)
    ·
      refine ⟨1244917113351865211768075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13279115875753228925526133 1244917113351865211768075)
      ·
        refine ⟨1867375670027797817652113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244917113351865211768075 1867375670027797817652113)
        ·
          refine ⟨1400531752520848363239085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1867375670027797817652113 1400531752520848363239085)
          ·
            refine ⟨525199407195318136214657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1400531752520848363239085 525199407195318136214657)
            ·
              refine ⟨393899555396488602160993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525199407195318136214657 393899555396488602160993)
              ·
                refine ⟨295424666547366451620745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393899555396488602160993 295424666547366451620745)
                ·
                  refine ⟨221568499910524838715559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295424666547366451620745 221568499910524838715559)
                  ·
                    rfl

theorem cell20_485441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 2].length) (baseStart_485441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485441 prefixEnd_485441 := by exact prefixLift 485441
  have htrace : WordTrace (prefixWord ++ tailWord_485441) baseStart_485441 baseEnd_485441 := by
    simpa [prefixWord, tailWord_485441, baseEnd_485441] using wordTrace_append hprefix tailTrace_485441
  have hstable : (prefixWord ++ tailWord_485441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485441).length < 2 ^ (prefixWord ++ tailWord_485441).sum := by decide
  have hdescent : baseEnd_485441 < baseStart_485441 := by decide
  rcases family_descends (prefixWord ++ tailWord_485441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485449 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 4]
def baseStart_485449 : Nat := 118140960795 + 485449 * 2 ^ 59
def prefixEnd_485449 : Nat := 4983230072969 + 3 ^ 40 * 485449 * 2
def baseEnd_485449 : Nat := 221572151328512366448859

theorem tailTrace_485449 : CollatzResearch.WordTrace tailWord_485449 prefixEnd_485449 221572151328512366448859 := by
  unfold tailWord_485449
  simp only [CollatzResearch.WordTrace]
  refine ⟨17705779618308655933659401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11803853078872437289106267 17705779618308655933659401)
  ·
    refine ⟨13279334713731491950244551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17705779618308655933659401 13279334713731491950244551)
    ·
      refine ⟨19919002070597237925366827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13279334713731491950244551 19919002070597237925366827)
      ·
        refine ⟨29878503105895856888050241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19919002070597237925366827 29878503105895856888050241)
        ·
          refine ⟨22408877329421892666037681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29878503105895856888050241 22408877329421892666037681)
          ·
            refine ⟨16806657997066419499528261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22408877329421892666037681 16806657997066419499528261)
            ·
              refine ⟨3151248374449953656161549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16806657997066419499528261 3151248374449953656161549)
              ·
                refine ⟨1181718140418732621060581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3151248374449953656161549 1181718140418732621060581)
                ·
                  refine ⟨221572151328512366448859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1181718140418732621060581 221572151328512366448859)
                  ·
                    rfl

theorem cell20_485449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_485449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485449 prefixEnd_485449 := by exact prefixLift 485449
  have htrace : WordTrace (prefixWord ++ tailWord_485449) baseStart_485449 baseEnd_485449 := by
    simpa [prefixWord, tailWord_485449, baseEnd_485449] using wordTrace_append hprefix tailTrace_485449
  have hstable : (prefixWord ++ tailWord_485449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485449).length < 2 ^ (prefixWord ++ tailWord_485449).sum := by decide
  have hdescent : baseEnd_485449 < baseStart_485449 := by decide
  rcases family_descends (prefixWord ++ tailWord_485449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485462 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_485462 : Nat := 118140960795 + 485462 * 2 ^ 59
def prefixEnd_485462 : Nat := 4983230072969 + 3 ^ 40 * 485462 * 2
def baseEnd_485462 : Nat := 221578084882742099015473

theorem tailTrace_485462 : CollatzResearch.WordTrace tailWord_485462 prefixEnd_485462 221578084882742099015473 := by
  unfold tailWord_485462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1106640860453847447117665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11804169178174372769255093 1106640860453847447117665)
  ·
    refine ⟨829980645340385585338249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1106640860453847447117665 829980645340385585338249)
    ·
      refine ⟨622485484005289189003687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 829980645340385585338249 622485484005289189003687)
      ·
        refine ⟨933728226007933783505531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622485484005289189003687 933728226007933783505531)
        ·
          refine ⟨1400592339011900675258297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933728226007933783505531 1400592339011900675258297)
          ·
            refine ⟨1050444254258925506443723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1400592339011900675258297 1050444254258925506443723)
            ·
              refine ⟨1575666381388388259665585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050444254258925506443723 1575666381388388259665585)
              ·
                refine ⟨1181749786041291194749189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1575666381388388259665585 1181749786041291194749189)
                ·
                  refine ⟨221578084882742099015473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1181749786041291194749189 221578084882742099015473)
                  ·
                    rfl

theorem cell20_485462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_485462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485462 prefixEnd_485462 := by exact prefixLift 485462
  have htrace : WordTrace (prefixWord ++ tailWord_485462) baseStart_485462 baseEnd_485462 := by
    simpa [prefixWord, tailWord_485462, baseEnd_485462] using wordTrace_append hprefix tailTrace_485462
  have hstable : (prefixWord ++ tailWord_485462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485462).length < 2 ^ (prefixWord ++ tailWord_485462).sum := by decide
  have hdescent : baseEnd_485462 < baseStart_485462 := by decide
  rcases family_descends (prefixWord ++ tailWord_485462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485469 : List Nat := [1, 4, 4, 1, 1, 2, 3, 4]
def baseStart_485469 : Nat := 118140960795 + 485469 * 2 ^ 59
def prefixEnd_485469 : Nat := 4983230072969 + 3 ^ 40 * 485469 * 2
def baseEnd_485469 : Nat := 73860426624493728594037

theorem tailTrace_485469 : CollatzResearch.WordTrace tailWord_485469 prefixEnd_485469 73860426624493728594037 := by
  unfold tailWord_485469
  simp only [CollatzResearch.WordTrace]
  refine ⟨17706509078236199349387461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11804339385490799566258307 17706509078236199349387461)
  ·
    refine ⟨3319970452169287378010149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17706509078236199349387461 3319970452169287378010149)
    ·
      refine ⟨622494459781741383376903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3319970452169287378010149 622494459781741383376903)
      ·
        refine ⟨933741689672612075065355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622494459781741383376903 933741689672612075065355)
        ·
          refine ⟨1400612534508918112598033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933741689672612075065355 1400612534508918112598033)
          ·
            refine ⟨1050459400881688584448525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1400612534508918112598033 1050459400881688584448525)
            ·
              refine ⟨393922275330633219168197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1050459400881688584448525 393922275330633219168197)
              ·
                refine ⟨73860426624493728594037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 393922275330633219168197 73860426624493728594037)
                ·
                  rfl

theorem cell20_485469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 4].length) (baseStart_485469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485469 prefixEnd_485469 := by exact prefixLift 485469
  have htrace : WordTrace (prefixWord ++ tailWord_485469) baseStart_485469 baseEnd_485469 := by
    simpa [prefixWord, tailWord_485469, baseEnd_485469] using wordTrace_append hprefix tailTrace_485469
  have hstable : (prefixWord ++ tailWord_485469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485469).length < 2 ^ (prefixWord ++ tailWord_485469).sum := by decide
  have hdescent : baseEnd_485469 < baseStart_485469 := by decide
  rcases family_descends (prefixWord ++ tailWord_485469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485497 : List Nat := [1, 2, 1, 3, 4, 1, 3, 2, 3]
def baseStart_485497 : Nat := 118140960795 + 485497 * 2 ^ 59
def prefixEnd_485497 : Nat := 4983230072969 + 3 ^ 40 * 485497 * 2
def baseEnd_485497 : Nat := 221594059836437532848663

theorem tailTrace_485497 : CollatzResearch.WordTrace tailWord_485497 prefixEnd_485497 221594059836437532848663 := by
  unfold tailWord_485497
  simp only [CollatzResearch.WordTrace]
  refine ⟨17707530322134760131406745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11805020214756506754271163 17707530322134760131406745)
  ·
    refine ⟨13280647741601070098555059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17707530322134760131406745 13280647741601070098555059)
    ·
      refine ⟨19920971612401605147832589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13280647741601070098555059 19920971612401605147832589)
      ·
        refine ⟨7470364354650601930437221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19920971612401605147832589 7470364354650601930437221)
        ·
          refine ⟨1400693316496987861956979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7470364354650601930437221 1400693316496987861956979)
          ·
            refine ⟨2101039974745481792935469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400693316496987861956979 2101039974745481792935469)
            ·
              refine ⟨787889990529555672350801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2101039974745481792935469 787889990529555672350801)
              ·
                refine ⟨590917492897166754263101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787889990529555672350801 590917492897166754263101)
                ·
                  refine ⟨221594059836437532848663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590917492897166754263101 221594059836437532848663)
                  ·
                    rfl

theorem cell20_485497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_485497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485497 prefixEnd_485497 := by exact prefixLift 485497
  have htrace : WordTrace (prefixWord ++ tailWord_485497) baseStart_485497 baseEnd_485497 := by
    simpa [prefixWord, tailWord_485497, baseEnd_485497] using wordTrace_append hprefix tailTrace_485497
  have hstable : (prefixWord ++ tailWord_485497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485497).length < 2 ^ (prefixWord ++ tailWord_485497).sum := by decide
  have hdescent : baseEnd_485497 < baseStart_485497 := by decide
  rcases family_descends (prefixWord ++ tailWord_485497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485514 : List Nat := [3, 1, 2, 3, 1, 3, 3, 1, 3]
def baseStart_485514 : Nat := 118140960795 + 485514 * 2 ^ 59
def prefixEnd_485514 : Nat := 4983230072969 + 3 ^ 40 * 485514 * 2
def baseEnd_485514 : Nat := 221601819099661029281927

theorem tailTrace_485514 : CollatzResearch.WordTrace tailWord_485514 prefixEnd_485514 221601819099661029281927 := by
  unfold tailWord_485514
  simp only [CollatzResearch.WordTrace]
  refine ⟨4427037590768293008693899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11805433575382114689850397 4427037590768293008693899)
  ·
    refine ⟨6640556386152439513040849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4427037590768293008693899 6640556386152439513040849)
    ·
      refine ⟨4980417289614329634780637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6640556386152439513040849 4980417289614329634780637)
      ·
        refine ⟨1867656483605373613042739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4980417289614329634780637 1867656483605373613042739)
        ·
          refine ⟨2801484725408060419564109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867656483605373613042739 2801484725408060419564109)
          ·
            refine ⟨1050556772028022657336541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2801484725408060419564109 1050556772028022657336541)
            ·
              refine ⟨393958789510508496501203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1050556772028022657336541 393958789510508496501203)
              ·
                refine ⟨590938184265762744751805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393958789510508496501203 590938184265762744751805)
                ·
                  refine ⟨221601819099661029281927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590938184265762744751805 221601819099661029281927)
                  ·
                    rfl

theorem cell20_485514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_485514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485514 prefixEnd_485514 := by exact prefixLift 485514
  have htrace : WordTrace (prefixWord ++ tailWord_485514) baseStart_485514 baseEnd_485514 := by
    simpa [prefixWord, tailWord_485514, baseEnd_485514] using wordTrace_append hprefix tailTrace_485514
  have hstable : (prefixWord ++ tailWord_485514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485514).length < 2 ^ (prefixWord ++ tailWord_485514).sum := by decide
  have hdescent : baseEnd_485514 < baseStart_485514 := by decide
  rcases family_descends (prefixWord ++ tailWord_485514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485524 : List Nat := [2, 4, 2, 3, 1, 2, 2, 4]
def baseStart_485524 : Nat := 118140960795 + 485524 * 2 ^ 59
def prefixEnd_485524 : Nat := 4983230072969 + 3 ^ 40 * 485524 * 2
def baseEnd_485524 : Nat := 73868794457381812982851

theorem tailTrace_485524 : CollatzResearch.WordTrace tailWord_485524 prefixEnd_485524 73868794457381812982851 := by
  unfold tailWord_485524
  simp only [CollatzResearch.WordTrace]
  refine ⟨8854257546518471871319813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11805676728691295828426417 8854257546518471871319813)
  ·
    refine ⟨1660173289972213475872465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8854257546518471871319813 1660173289972213475872465)
    ·
      refine ⟨1245129967479160106904349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1660173289972213475872465 1245129967479160106904349)
      ·
        refine ⟨466923737804685040089131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1245129967479160106904349 466923737804685040089131)
        ·
          refine ⟨700385606707027560133697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466923737804685040089131 700385606707027560133697)
          ·
            refine ⟨525289205030270670100273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 700385606707027560133697 525289205030270670100273)
            ·
              refine ⟨393966903772703002575205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525289205030270670100273 393966903772703002575205)
              ·
                refine ⟨73868794457381812982851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 393966903772703002575205 73868794457381812982851)
                ·
                  rfl

theorem cell20_485524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_485524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485524 prefixEnd_485524 := by exact prefixLift 485524
  have htrace : WordTrace (prefixWord ++ tailWord_485524) baseStart_485524 baseEnd_485524 := by
    simpa [prefixWord, tailWord_485524, baseEnd_485524] using wordTrace_append hprefix tailTrace_485524
  have hstable : (prefixWord ++ tailWord_485524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485524).length < 2 ^ (prefixWord ++ tailWord_485524).sum := by decide
  have hdescent : baseEnd_485524 < baseStart_485524 := by decide
  rcases family_descends (prefixWord ++ tailWord_485524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485525 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 4]
def baseStart_485525 : Nat := 118140960795 + 485525 * 2 ^ 59
def prefixEnd_485525 : Nat := 4983230072969 + 3 ^ 40 * 485525 * 2
def baseEnd_485525 : Nat := 221606839799393879915215

theorem tailTrace_485525 : CollatzResearch.WordTrace tailWord_485525 prefixEnd_485525 221606839799393879915215 := by
  unfold tailWord_485525
  simp only [CollatzResearch.WordTrace]
  refine ⟨17708551566033320913426029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11805701044022213942284019 17708551566033320913426029)
  ·
    refine ⟨6640706837262495342534761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17708551566033320913426029 6640706837262495342534761)
    ·
      refine ⟨4980530127946871506901071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6640706837262495342534761 4980530127946871506901071)
      ·
        refine ⟨7470795191920307260351607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4980530127946871506901071 7470795191920307260351607)
        ·
          refine ⟨11206192787880460890527411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7470795191920307260351607 11206192787880460890527411)
          ·
            refine ⟨16809289181820691335791117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11206192787880460890527411 16809289181820691335791117)
            ·
              refine ⟨6303483443182759250921669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16809289181820691335791117 6303483443182759250921669)
              ·
                refine ⟨1181903145596767359547813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6303483443182759250921669 1181903145596767359547813)
                ·
                  refine ⟨221606839799393879915215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1181903145596767359547813 221606839799393879915215)
                  ·
                    rfl

theorem cell20_485525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_485525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485525 prefixEnd_485525 := by exact prefixLift 485525
  have htrace : WordTrace (prefixWord ++ tailWord_485525) baseStart_485525 baseEnd_485525 := by
    simpa [prefixWord, tailWord_485525, baseEnd_485525] using wordTrace_append hprefix tailTrace_485525
  have hstable : (prefixWord ++ tailWord_485525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485525).length < 2 ^ (prefixWord ++ tailWord_485525).sum := by decide
  have hdescent : baseEnd_485525 < baseStart_485525 := by decide
  rcases family_descends (prefixWord ++ tailWord_485525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485534 : List Nat := [4, 3, 1, 1, 4, 1, 1, 3, 2]
def baseStart_485534 : Nat := 118140960795 + 485534 * 2 ^ 59
def prefixEnd_485534 : Nat := 4983230072969 + 3 ^ 40 * 485534 * 2
def baseEnd_485534 : Nat := 221610947644629848615179

theorem tailTrace_485534 : CollatzResearch.WordTrace tailWord_485534 prefixEnd_485534 221610947644629848615179 := by
  unfold tailWord_485534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2213609977875089431312957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11805919882000476967002437 2213609977875089431312957)
  ·
    refine ⟨830103741703158536742359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2213609977875089431312957 830103741703158536742359)
    ·
      refine ⟨1245155612554737805113539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 830103741703158536742359 1245155612554737805113539)
      ·
        refine ⟨1867733418832106707670309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245155612554737805113539 1867733418832106707670309)
        ·
          refine ⟨350200016031020007688183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1867733418832106707670309 350200016031020007688183)
          ·
            refine ⟨525300024046530011532275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350200016031020007688183 525300024046530011532275)
            ·
              refine ⟨787950036069795017298413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525300024046530011532275 787950036069795017298413)
              ·
                refine ⟨295481263526173131486905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 787950036069795017298413 295481263526173131486905)
                ·
                  refine ⟨221610947644629848615179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295481263526173131486905 221610947644629848615179)
                  ·
                    rfl

theorem cell20_485534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_485534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485534 prefixEnd_485534 := by exact prefixLift 485534
  have htrace : WordTrace (prefixWord ++ tailWord_485534) baseStart_485534 baseEnd_485534 := by
    simpa [prefixWord, tailWord_485534, baseEnd_485534] using wordTrace_append hprefix tailTrace_485534
  have hstable : (prefixWord ++ tailWord_485534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485534).length < 2 ^ (prefixWord ++ tailWord_485534).sum := by decide
  have hdescent : baseEnd_485534 < baseStart_485534 := by decide
  rcases family_descends (prefixWord ++ tailWord_485534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485538 : List Nat := [3, 3, 1, 3, 1, 1, 3, 3, 2]
def baseStart_485538 : Nat := 118140960795 + 485538 * 2 ^ 59
def prefixEnd_485538 : Nat := 4983230072969 + 3 ^ 40 * 485538 * 2
def baseEnd_485538 : Nat := 221612773353623612481829

theorem tailTrace_485538 : CollatzResearch.WordTrace tailWord_485538 prefixEnd_485538 221612773353623612481829 := by
  unfold tailWord_485538
  simp only [CollatzResearch.WordTrace]
  refine ⟨4427256428746556033412317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11806017143324149422432845 4427256428746556033412317)
  ·
    refine ⟨1660221160779958512529619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4427256428746556033412317 1660221160779958512529619)
    ·
      refine ⟨2490331741169937768794429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1660221160779958512529619 2490331741169937768794429)
      ·
        refine ⟨933874402938726663297911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2490331741169937768794429 933874402938726663297911)
        ·
          refine ⟨1400811604408089994946867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933874402938726663297911 1400811604408089994946867)
          ·
            refine ⟨2101217406612134992420301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400811604408089994946867 2101217406612134992420301)
            ·
              refine ⟨787956527479550622157613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2101217406612134992420301 787956527479550622157613)
              ·
                refine ⟨295483697804831483309105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 787956527479550622157613 295483697804831483309105)
                ·
                  refine ⟨221612773353623612481829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295483697804831483309105 221612773353623612481829)
                  ·
                    rfl

theorem cell20_485538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_485538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485538 prefixEnd_485538 := by exact prefixLift 485538
  have htrace : WordTrace (prefixWord ++ tailWord_485538) baseStart_485538 baseEnd_485538 := by
    simpa [prefixWord, tailWord_485538, baseEnd_485538] using wordTrace_append hprefix tailTrace_485538
  have hstable : (prefixWord ++ tailWord_485538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485538).length < 2 ^ (prefixWord ++ tailWord_485538).sum := by decide
  have hdescent : baseEnd_485538 < baseStart_485538 := by decide
  rcases family_descends (prefixWord ++ tailWord_485538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485549 : List Nat := [1, 5, 2, 1, 2, 1, 8]
def baseStart_485549 : Nat := 118140960795 + 485549 * 2 ^ 59
def prefixEnd_485549 : Nat := 4983230072969 + 3 ^ 40 * 485549 * 2
def baseEnd_485549 : Nat := 24624199339261829235013

theorem tailTrace_485549 : CollatzResearch.WordTrace tailWord_485549 prefixEnd_485549 24624199339261829235013 := by
  unfold tailWord_485549
  simp only [CollatzResearch.WordTrace]
  refine ⟨17709426917946373012299701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11806284611964248674866467 17709426917946373012299701)
  ·
    refine ⟨1660258773557472469903097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17709426917946373012299701 1660258773557472469903097)
    ·
      refine ⟨1245194080168104352427323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1660258773557472469903097 1245194080168104352427323)
      ·
        refine ⟨1867791120252156528640985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245194080168104352427323 1867791120252156528640985)
        ·
          refine ⟨1400843340189117396480739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1867791120252156528640985 1400843340189117396480739)
          ·
            refine ⟨2101265010283676094721109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400843340189117396480739 2101265010283676094721109)
            ·
              refine ⟨24624199339261829235013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2101265010283676094721109 24624199339261829235013)
              ·
                rfl

theorem cell20_485549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 8].length) (baseStart_485549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485549 prefixEnd_485549 := by exact prefixLift 485549
  have htrace : WordTrace (prefixWord ++ tailWord_485549) baseStart_485549 baseEnd_485549 := by
    simpa [prefixWord, tailWord_485549, baseEnd_485549] using wordTrace_append hprefix tailTrace_485549
  have hstable : (prefixWord ++ tailWord_485549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485549).length < 2 ^ (prefixWord ++ tailWord_485549).sum := by decide
  have hdescent : baseEnd_485549 < baseStart_485549 := by decide
  rcases family_descends (prefixWord ++ tailWord_485549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485566 : List Nat := [4, 2, 1, 1, 4, 1, 2, 5]
def baseStart_485566 : Nat := 118140960795 + 485566 * 2 ^ 59
def prefixEnd_485566 : Nat := 4983230072969 + 3 ^ 40 * 485566 * 2
def baseEnd_485566 : Nat := 73875184438859986516127

theorem tailTrace_485566 : CollatzResearch.WordTrace tailWord_485566 prefixEnd_485566 73875184438859986516127 := by
  unfold tailWord_485566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2213755869860598114458569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11806697972589856610445701 2213755869860598114458569)
  ·
    refine ⟨1660316902395448585843927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2213755869860598114458569 1660316902395448585843927)
    ·
      refine ⟨2490475353593172878765891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1660316902395448585843927 2490475353593172878765891)
      ·
        refine ⟨3735713030389759318148837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2490475353593172878765891 3735713030389759318148837)
        ·
          refine ⟨700446193198079872152907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3735713030389759318148837 700446193198079872152907)
          ·
            refine ⟨1050669289797119808229361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700446193198079872152907 1050669289797119808229361)
            ·
              refine ⟨788001967347839856172021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1050669289797119808229361 788001967347839856172021)
              ·
                refine ⟨73875184438859986516127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 788001967347839856172021 73875184438859986516127)
                ·
                  rfl

theorem cell20_485566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_485566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485566 prefixEnd_485566 := by exact prefixLift 485566
  have htrace : WordTrace (prefixWord ++ tailWord_485566) baseStart_485566 baseEnd_485566 := by
    simpa [prefixWord, tailWord_485566, baseEnd_485566] using wordTrace_append hprefix tailTrace_485566
  have hstable : (prefixWord ++ tailWord_485566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485566).length < 2 ^ (prefixWord ++ tailWord_485566).sum := by decide
  have hdescent : baseEnd_485566 < baseStart_485566 := by decide
  rcases family_descends (prefixWord ++ tailWord_485566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485573 : List Nat := [1, 3, 1, 1, 1, 1, 8, 1, 3]
def baseStart_485573 : Nat := 118140960795 + 485573 * 2 ^ 59
def prefixEnd_485573 : Nat := 4983230072969 + 3 ^ 40 * 485573 * 2
def baseEnd_485573 : Nat := 221628748307319046315019

theorem tailTrace_485573 : CollatzResearch.WordTrace tailWord_485573 prefixEnd_485573 221628748307319046315019 := by
  unfold tailWord_485573
  simp only [CollatzResearch.WordTrace]
  refine ⟨17710302269859425111173373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11806868179906283407448915 17710302269859425111173373)
  ·
    refine ⟨6641363351197284416690015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17710302269859425111173373 6641363351197284416690015)
    ·
      refine ⟨9962045026795926625035023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6641363351197284416690015 9962045026795926625035023)
      ·
        refine ⟨14943067540193889937552535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9962045026795926625035023 14943067540193889937552535)
        ·
          refine ⟨22414601310290834906328803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14943067540193889937552535 22414601310290834906328803)
          ·
            refine ⟨33621901965436252359493205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22414601310290834906328803 33621901965436252359493205)
            ·
              refine ⟨394006663657456082337811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 33621901965436252359493205 394006663657456082337811)
              ·
                refine ⟨591009995486184123506717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394006663657456082337811 591009995486184123506717)
                ·
                  refine ⟨221628748307319046315019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591009995486184123506717 221628748307319046315019)
                  ·
                    rfl

theorem cell20_485573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_485573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485573 prefixEnd_485573 := by exact prefixLift 485573
  have htrace : WordTrace (prefixWord ++ tailWord_485573) baseStart_485573 baseEnd_485573 := by
    simpa [prefixWord, tailWord_485573, baseEnd_485573] using wordTrace_append hprefix tailTrace_485573
  have hstable : (prefixWord ++ tailWord_485573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485573).length < 2 ^ (prefixWord ++ tailWord_485573).sum := by decide
  have hdescent : baseEnd_485573 < baseStart_485573 := by decide
  rcases family_descends (prefixWord ++ tailWord_485573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485577 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 7]
def baseStart_485577 : Nat := 118140960795 + 485577 * 2 ^ 59
def prefixEnd_485577 : Nat := 4983230072969 + 3 ^ 40 * 485577 * 2
def baseEnd_485577 : Nat := 221630574016312810181669

theorem tailTrace_485577 : CollatzResearch.WordTrace tailWord_485577 prefixEnd_485577 221630574016312810181669 := by
  unfold tailWord_485577
  simp only [CollatzResearch.WordTrace]
  refine ⟨17710448161844933794318985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11806965441229955862879323 17710448161844933794318985)
  ·
    refine ⟨13282836121383700345739239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17710448161844933794318985 13282836121383700345739239)
    ·
      refine ⟨19924254182075550518608859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13282836121383700345739239 19924254182075550518608859)
      ·
        refine ⟨29886381273113325777913289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19924254182075550518608859 29886381273113325777913289)
        ·
          refine ⟨22414785954834994333434967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29886381273113325777913289 22414785954834994333434967)
          ·
            refine ⟨33622178932252491500152451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22414785954834994333434967 33622178932252491500152451)
            ·
              refine ⟨50433268398378737250228677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33622178932252491500152451 50433268398378737250228677)
              ·
                refine ⟨9456237824696013234417877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50433268398378737250228677 9456237824696013234417877)
                ·
                  refine ⟨221630574016312810181669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9456237824696013234417877 221630574016312810181669)
                  ·
                    rfl

theorem cell20_485577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_485577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485577 prefixEnd_485577 := by exact prefixLift 485577
  have htrace : WordTrace (prefixWord ++ tailWord_485577) baseStart_485577 baseEnd_485577 := by
    simpa [prefixWord, tailWord_485577, baseEnd_485577] using wordTrace_append hprefix tailTrace_485577
  have hstable : (prefixWord ++ tailWord_485577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485577).length < 2 ^ (prefixWord ++ tailWord_485577).sum := by decide
  have hdescent : baseEnd_485577 < baseStart_485577 := by decide
  rcases family_descends (prefixWord ++ tailWord_485577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485608 : List Nat := [2, 1, 4, 1, 2, 10]
def baseStart_485608 : Nat := 118140960795 + 485608 * 2 ^ 59
def prefixEnd_485608 : Nat := 4983230072969 + 3 ^ 40 * 485608 * 2
def baseEnd_485608 : Nat := 8209063824482017783267

theorem tailTrace_485608 : CollatzResearch.WordTrace tailWord_485608 prefixEnd_485608 8209063824482017783267 := by
  unfold tailWord_485608
  simp only [CollatzResearch.WordTrace]
  refine ⟨8855789412366313044348739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11807719216488417392464985 8855789412366313044348739)
  ·
    refine ⟨13283684118549469566523109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8855789412366313044348739 13283684118549469566523109)
    ·
      refine ⟨2490690772228025543723083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13283684118549469566523109 2490690772228025543723083)
      ·
        refine ⟨3736036158342038315584625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2490690772228025543723083 3736036158342038315584625)
        ·
          refine ⟨2802027118756528736688469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3736036158342038315584625 2802027118756528736688469)
          ·
            refine ⟨8209063824482017783267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2802027118756528736688469 8209063824482017783267)
            ·
              rfl

theorem cell20_485608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 10].length) (baseStart_485608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485608 prefixEnd_485608 := by exact prefixLift 485608
  have htrace : WordTrace (prefixWord ++ tailWord_485608) baseStart_485608 baseEnd_485608 := by
    simpa [prefixWord, tailWord_485608, baseEnd_485608] using wordTrace_append hprefix tailTrace_485608
  have hstable : (prefixWord ++ tailWord_485608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485608).length < 2 ^ (prefixWord ++ tailWord_485608).sum := by decide
  have hdescent : baseEnd_485608 < baseStart_485608 := by decide
  rcases family_descends (prefixWord ++ tailWord_485608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485632 : List Nat := [2, 1, 1, 2, 1, 1, 6, 3, 3]
def baseStart_485632 : Nat := 118140960795 + 485632 * 2 ^ 59
def prefixEnd_485632 : Nat := 4983230072969 + 3 ^ 40 * 485632 * 2
def baseEnd_485632 : Nat := 221655677514977063348111

theorem tailTrace_485632 : CollatzResearch.WordTrace tailWord_485632 prefixEnd_485632 221655677514977063348111 := by
  unfold tailWord_485632
  simp only [CollatzResearch.WordTrace]
  refine ⟨8856227088322839093785575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11808302784430452125047433 8856227088322839093785575)
  ·
    refine ⟨13284340632484258640678363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8856227088322839093785575 13284340632484258640678363)
    ·
      refine ⟨19926510948726387961017545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13284340632484258640678363 19926510948726387961017545)
      ·
        refine ⟨14944883211544790970763159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19926510948726387961017545 14944883211544790970763159)
        ·
          refine ⟨22417324817317186456144739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14944883211544790970763159 22417324817317186456144739)
          ·
            refine ⟨33625987225975779684217109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22417324817317186456144739 33625987225975779684217109)
            ·
              refine ⟨1576218151217614672697677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33625987225975779684217109 1576218151217614672697677)
              ·
                refine ⟨591081806706605502261629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1576218151217614672697677 591081806706605502261629)
                ·
                  refine ⟨221655677514977063348111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591081806706605502261629 221655677514977063348111)
                  ·
                    rfl

theorem cell20_485632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_485632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485632 prefixEnd_485632 := by exact prefixLift 485632
  have htrace : WordTrace (prefixWord ++ tailWord_485632) baseStart_485632 baseEnd_485632 := by
    simpa [prefixWord, tailWord_485632, baseEnd_485632] using wordTrace_append hprefix tailTrace_485632
  have hstable : (prefixWord ++ tailWord_485632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485632).length < 2 ^ (prefixWord ++ tailWord_485632).sum := by decide
  have hdescent : baseEnd_485632 < baseStart_485632 := by decide
  rcases family_descends (prefixWord ++ tailWord_485632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485666 : List Nat := [3, 3, 1, 1, 3, 3, 1, 2, 3]
def baseStart_485666 : Nat := 118140960795 + 485666 * 2 ^ 59
def prefixEnd_485666 : Nat := 4983230072969 + 3 ^ 40 * 485666 * 2
def baseEnd_485666 : Nat := 221671196041424056214639

theorem tailTrace_485666 : CollatzResearch.WordTrace tailWord_485666 prefixEnd_485666 221671196041424056214639 := by
  unfold tailWord_485666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4428423564630625498577213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11809129505681667996205901 4428423564630625498577213)
  ·
    refine ⟨1660658836736484561966455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4428423564630625498577213 1660658836736484561966455)
    ·
      refine ⟨2490988255104726842949683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1660658836736484561966455 2490988255104726842949683)
      ·
        refine ⟨3736482382657090264424525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2490988255104726842949683 3736482382657090264424525)
        ·
          refine ⟨1401180893496408849159197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3736482382657090264424525 1401180893496408849159197)
          ·
            refine ⟨525442835061153318434699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1401180893496408849159197 525442835061153318434699)
            ·
              refine ⟨788164252591729977652049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525442835061153318434699 788164252591729977652049)
              ·
                refine ⟨591123189443797483239037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788164252591729977652049 591123189443797483239037)
                ·
                  refine ⟨221671196041424056214639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591123189443797483239037 221671196041424056214639)
                  ·
                    rfl

theorem cell20_485666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_485666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485666 prefixEnd_485666 := by exact prefixLift 485666
  have htrace : WordTrace (prefixWord ++ tailWord_485666) baseStart_485666 baseEnd_485666 := by
    simpa [prefixWord, tailWord_485666, baseEnd_485666] using wordTrace_append hprefix tailTrace_485666
  have hstable : (prefixWord ++ tailWord_485666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485666).length < 2 ^ (prefixWord ++ tailWord_485666).sum := by decide
  have hdescent : baseEnd_485666 < baseStart_485666 := by decide
  rcases family_descends (prefixWord ++ tailWord_485666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485694 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_485694 : Nat := 118140960795 + 485694 * 2 ^ 59
def prefixEnd_485694 : Nat := 4983230072969 + 3 ^ 40 * 485694 * 2
def baseEnd_485694 : Nat := 221683976004380403281191

theorem tailTrace_485694 : CollatzResearch.WordTrace tailWord_485694 prefixEnd_485694 221683976004380403281191 := by
  unfold tailWord_485694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2214339437802632847041017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11809810334947375184218757 2214339437802632847041017)
  ·
    refine ⟨1660754578351974635280763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2214339437802632847041017 1660754578351974635280763)
    ·
      refine ⟨2491131867527961952921145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1660754578351974635280763 2491131867527961952921145)
      ·
        refine ⟨1868348900645971464690859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2491131867527961952921145 1868348900645971464690859)
        ·
          refine ⟨2802523350968957197036289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868348900645971464690859 2802523350968957197036289)
          ·
            refine ⟨2101892513226717897777217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2802523350968957197036289 2101892513226717897777217)
            ·
              refine ⟨1576419384920038423332913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2101892513226717897777217 1576419384920038423332913)
              ·
                refine ⟨1182314538690028817499685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576419384920038423332913 1182314538690028817499685)
                ·
                  refine ⟨221683976004380403281191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1182314538690028817499685 221683976004380403281191)
                  ·
                    rfl

theorem cell20_485694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_485694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485694 prefixEnd_485694 := by exact prefixLift 485694
  have htrace : WordTrace (prefixWord ++ tailWord_485694) baseStart_485694 baseEnd_485694 := by
    simpa [prefixWord, tailWord_485694, baseEnd_485694] using wordTrace_append hprefix tailTrace_485694
  have hstable : (prefixWord ++ tailWord_485694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485694).length < 2 ^ (prefixWord ++ tailWord_485694).sum := by decide
  have hdescent : baseEnd_485694 < baseStart_485694 := by decide
  rcases family_descends (prefixWord ++ tailWord_485694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485697 : List Nat := [1, 2, 5, 2, 2, 2, 2, 4]
def baseStart_485697 : Nat := 118140960795 + 485697 * 2 ^ 59
def prefixEnd_485697 : Nat := 4983230072969 + 3 ^ 40 * 485697 * 2
def baseEnd_485697 : Nat := 73895115095375242060393

theorem tailTrace_485697 : CollatzResearch.WordTrace tailWord_485697 prefixEnd_485697 73895115095375242060393 := by
  unfold tailWord_485697
  simp only [CollatzResearch.WordTrace]
  refine ⟨17714824921410194288687345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11809883280940129525791563 17714824921410194288687345)
  ·
    refine ⟨13286118691057645716515509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17714824921410194288687345 13286118691057645716515509)
    ·
      refine ⟨1245573627286654285923329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13286118691057645716515509 1245573627286654285923329)
      ·
        refine ⟨934180220464990714442497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1245573627286654285923329 934180220464990714442497)
        ·
          refine ⟨700635165348743035831873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 934180220464990714442497 700635165348743035831873)
          ·
            refine ⟨525476374011557276873905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 700635165348743035831873 525476374011557276873905)
            ·
              refine ⟨394107280508667957655429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525476374011557276873905 394107280508667957655429)
              ·
                refine ⟨73895115095375242060393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394107280508667957655429 73895115095375242060393)
                ·
                  rfl

theorem cell20_485697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 4].length) (baseStart_485697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485697 prefixEnd_485697 := by exact prefixLift 485697
  have htrace : WordTrace (prefixWord ++ tailWord_485697) baseStart_485697 baseEnd_485697 := by
    simpa [prefixWord, tailWord_485697, baseEnd_485697] using wordTrace_append hprefix tailTrace_485697
  have hstable : (prefixWord ++ tailWord_485697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485697).length < 2 ^ (prefixWord ++ tailWord_485697).sum := by decide
  have hdescent : baseEnd_485697 < baseStart_485697 := by decide
  rcases family_descends (prefixWord ++ tailWord_485697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485728 : List Nat := [2, 1, 1, 3, 5, 1, 3, 2, 2]
def baseStart_485728 : Nat := 118140960795 + 485728 * 2 ^ 59
def prefixEnd_485728 : Nat := 4983230072969 + 3 ^ 40 * 485728 * 2
def baseEnd_485728 : Nat := 221699494530827396147719

theorem tailTrace_485728 : CollatzResearch.WordTrace tailWord_485728 prefixEnd_485728 221699494530827396147719 := by
  unfold tailWord_485728
  simp only [CollatzResearch.WordTrace]
  refine ⟨8857977792148943291532919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11810637056198591055377225 8857977792148943291532919)
  ·
    refine ⟨13286966688223414937299379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8857977792148943291532919 13286966688223414937299379)
    ·
      refine ⟨19930450032335122405949069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13286966688223414937299379 19930450032335122405949069)
      ·
        refine ⟨7473918762125670902230901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19930450032335122405949069 7473918762125670902230901)
        ·
          refine ⟨700679883949281647084147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7473918762125670902230901 700679883949281647084147)
          ·
            refine ⟨1051019825923922470626221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700679883949281647084147 1051019825923922470626221)
            ·
              refine ⟨394132434721470926484833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1051019825923922470626221 394132434721470926484833)
              ·
                refine ⟨295599326041103194863625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394132434721470926484833 295599326041103194863625)
                ·
                  refine ⟨221699494530827396147719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295599326041103194863625 221699494530827396147719)
                  ·
                    rfl

theorem cell20_485728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 2].length) (baseStart_485728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485728 prefixEnd_485728 := by exact prefixLift 485728
  have htrace : WordTrace (prefixWord ++ tailWord_485728) baseStart_485728 baseEnd_485728 := by
    simpa [prefixWord, tailWord_485728, baseEnd_485728] using wordTrace_append hprefix tailTrace_485728
  have hstable : (prefixWord ++ tailWord_485728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485728).length < 2 ^ (prefixWord ++ tailWord_485728).sum := by decide
  have hdescent : baseEnd_485728 < baseStart_485728 := by decide
  rcases family_descends (prefixWord ++ tailWord_485728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485780 : List Nat := [2, 4, 2, 1, 3, 1, 2, 2, 3]
def baseStart_485780 : Nat := 118140960795 + 485780 * 2 ^ 59
def prefixEnd_485780 : Nat := 4983230072969 + 3 ^ 40 * 485780 * 2
def baseEnd_485780 : Nat := 221723228747746326414173

theorem tailTrace_485780 : CollatzResearch.WordTrace tailWord_485780 prefixEnd_485780 221723228747746326414173 := by
  unfold tailWord_485780
  simp only [CollatzResearch.WordTrace]
  refine ⟨8858926090054749731979397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11811901453406332975972529 8858926090054749731979397)
  ·
    refine ⟨1661048641885265574746137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8858926090054749731979397 1661048641885265574746137)
    ·
      refine ⟨1245786481413949181059603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1661048641885265574746137 1245786481413949181059603)
      ·
        refine ⟨1868679722120923771589405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245786481413949181059603 1868679722120923771589405)
        ·
          refine ⟨700754895795346414346027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1868679722120923771589405 700754895795346414346027)
          ·
            refine ⟨1051132343693019621519041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700754895795346414346027 1051132343693019621519041)
            ·
              refine ⟨788349257769764716139281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051132343693019621519041 788349257769764716139281)
              ·
                refine ⟨591261943327323537104461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788349257769764716139281 591261943327323537104461)
                ·
                  refine ⟨221723228747746326414173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591261943327323537104461 221723228747746326414173)
                  ·
                    rfl

theorem cell20_485780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_485780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485780 prefixEnd_485780 := by exact prefixLift 485780
  have htrace : WordTrace (prefixWord ++ tailWord_485780) baseStart_485780 baseEnd_485780 := by
    simpa [prefixWord, tailWord_485780, baseEnd_485780] using wordTrace_append hprefix tailTrace_485780
  have hstable : (prefixWord ++ tailWord_485780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485780).length < 2 ^ (prefixWord ++ tailWord_485780).sum := by decide
  have hdescent : baseEnd_485780 < baseStart_485780 := by decide
  rcases family_descends (prefixWord ++ tailWord_485780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485791 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 4]
def baseStart_485791 : Nat := 118140960795 + 485791 * 2 ^ 59
def prefixEnd_485791 : Nat := 4983230072969 + 3 ^ 40 * 485791 * 2
def baseEnd_485791 : Nat := 221728249447479177047461

theorem tailTrace_485791 : CollatzResearch.WordTrace tailWord_485791 prefixEnd_485791 221728249447479177047461 := by
  unfold tailWord_485791
  simp only [CollatzResearch.WordTrace]
  refine ⟨17718253383069648342609227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11812168922046432228406151 17718253383069648342609227)
  ·
    refine ⟨26577380074604472513913841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17718253383069648342609227 26577380074604472513913841)
    ·
      refine ⟨19933035055953354385435381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26577380074604472513913841 19933035055953354385435381)
      ·
        refine ⟨1868722036495626973634567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19933035055953354385435381 1868722036495626973634567)
        ·
          refine ⟨2803083054743440460451851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868722036495626973634567 2803083054743440460451851)
          ·
            refine ⟨4204624582115160690677777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2803083054743440460451851 4204624582115160690677777)
            ·
              refine ⟨3153468436586370518008333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4204624582115160690677777 3153468436586370518008333)
              ·
                refine ⟨1182550663719888944253125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3153468436586370518008333 1182550663719888944253125)
                ·
                  refine ⟨221728249447479177047461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1182550663719888944253125 221728249447479177047461)
                  ·
                    rfl

theorem cell20_485791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_485791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485791 prefixEnd_485791 := by exact prefixLift 485791
  have htrace : WordTrace (prefixWord ++ tailWord_485791) baseStart_485791 baseEnd_485791 := by
    simpa [prefixWord, tailWord_485791, baseEnd_485791] using wordTrace_append hprefix tailTrace_485791
  have hstable : (prefixWord ++ tailWord_485791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485791).length < 2 ^ (prefixWord ++ tailWord_485791).sum := by decide
  have hdescent : baseEnd_485791 < baseStart_485791 := by decide
  rcases family_descends (prefixWord ++ tailWord_485791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485815 : List Nat := [1, 1, 3, 1, 3, 4, 3, 4]
def baseStart_485815 : Nat := 118140960795 + 485815 * 2 ^ 59
def prefixEnd_485815 : Nat := 4983230072969 + 3 ^ 40 * 485815 * 2
def baseEnd_485815 : Nat := 73913067900480586749121

theorem tailTrace_485815 : CollatzResearch.WordTrace tailWord_485815 prefixEnd_485815 73913067900480586749121 := by
  unfold tailWord_485815
  simp only [CollatzResearch.WordTrace]
  refine ⟨17719128734982700441482899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11812752489988466960988599 17719128734982700441482899)
  ·
    refine ⟨26578693102474050662224349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17719128734982700441482899 26578693102474050662224349)
    ·
      refine ⟨9967009913427768998334131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26578693102474050662224349 9967009913427768998334131)
      ·
        refine ⟨14950514870141653497501197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9967009913427768998334131 14950514870141653497501197)
        ·
          refine ⟨5606443076303120061562949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14950514870141653497501197 5606443076303120061562949)
          ·
            refine ⟨1051208076806835011543053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5606443076303120061562949 1051208076806835011543053)
            ·
              refine ⟨394203028802563129328645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1051208076806835011543053 394203028802563129328645)
              ·
                refine ⟨73913067900480586749121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394203028802563129328645 73913067900480586749121)
                ·
                  rfl

theorem cell20_485815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 4].length) (baseStart_485815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485815 prefixEnd_485815 := by exact prefixLift 485815
  have htrace : WordTrace (prefixWord ++ tailWord_485815) baseStart_485815 baseEnd_485815 := by
    simpa [prefixWord, tailWord_485815, baseEnd_485815] using wordTrace_append hprefix tailTrace_485815
  have hstable : (prefixWord ++ tailWord_485815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485815).length < 2 ^ (prefixWord ++ tailWord_485815).sum := by decide
  have hdescent : baseEnd_485815 < baseStart_485815 := by decide
  rcases family_descends (prefixWord ++ tailWord_485815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485870 : List Nat := [4, 1, 2, 1, 2, 4, 2, 4]
def baseStart_485870 : Nat := 118140960795 + 485870 * 2 ^ 59
def prefixEnd_485870 : Nat := 4983230072969 + 3 ^ 40 * 485870 * 2
def baseEnd_485870 : Nat := 73921435733368671137935

theorem tailTrace_485870 : CollatzResearch.WordTrace tailWord_485870 prefixEnd_485870 73921435733368671137935 := by
  unfold tailWord_485870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2215141843722930604341883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11814089833188963223156709 2215141843722930604341883)
  ·
    refine ⟨3322712765584395906512825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2215141843722930604341883 3322712765584395906512825)
    ·
      refine ⟨2492034574188296929884619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3322712765584395906512825 2492034574188296929884619)
      ·
        refine ⟨3738051861282445394826929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2492034574188296929884619 3738051861282445394826929)
        ·
          refine ⟨2803538895961834046120197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3738051861282445394826929 2803538895961834046120197)
          ·
            refine ⟨525663542992843883647537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2803538895961834046120197 525663542992843883647537)
            ·
              refine ⟨394247657244632912735653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525663542992843883647537 394247657244632912735653)
              ·
                refine ⟨73921435733368671137935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394247657244632912735653 73921435733368671137935)
                ·
                  rfl

theorem cell20_485870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_485870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485870 prefixEnd_485870 := by exact prefixLift 485870
  have htrace : WordTrace (prefixWord ++ tailWord_485870) baseStart_485870 baseEnd_485870 := by
    simpa [prefixWord, tailWord_485870, baseEnd_485870] using wordTrace_append hprefix tailTrace_485870
  have hstable : (prefixWord ++ tailWord_485870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485870).length < 2 ^ (prefixWord ++ tailWord_485870).sum := by decide
  have hdescent : baseEnd_485870 < baseStart_485870 := by decide
  rcases family_descends (prefixWord ++ tailWord_485870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485881 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 5]
def baseStart_485881 : Nat := 118140960795 + 485881 * 2 ^ 59
def prefixEnd_485881 : Nat := 4983230072969 + 3 ^ 40 * 485881 * 2
def baseEnd_485881 : Nat := 221769327899838864047093

theorem tailTrace_485881 : CollatzResearch.WordTrace tailWord_485881 prefixEnd_485881 221769327899838864047093 := by
  unfold tailWord_485881
  simp only [CollatzResearch.WordTrace]
  refine ⟨17721535952743593713385497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11814357301829062475590331 17721535952743593713385497)
  ·
    refine ⟨13291151964557695285039123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17721535952743593713385497 13291151964557695285039123)
    ·
      refine ⟨19936727946836542927558685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13291151964557695285039123 19936727946836542927558685)
      ·
        refine ⟨7476272980063703597834507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19936727946836542927558685 7476272980063703597834507)
        ·
          refine ⟨11214409470095555396751761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7476272980063703597834507 11214409470095555396751761)
          ·
            refine ⟨8410807102571666547563821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11214409470095555396751761 8410807102571666547563821)
            ·
              refine ⟨3154052663464374955336433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8410807102571666547563821 3154052663464374955336433)
              ·
                refine ⟨2365539497598281216502325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3154052663464374955336433 2365539497598281216502325)
                ·
                  refine ⟨221769327899838864047093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2365539497598281216502325 221769327899838864047093)
                  ·
                    rfl

theorem cell20_485881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_485881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485881 prefixEnd_485881 := by exact prefixLift 485881
  have htrace : WordTrace (prefixWord ++ tailWord_485881) baseStart_485881 baseEnd_485881 := by
    simpa [prefixWord, tailWord_485881, baseEnd_485881] using wordTrace_append hprefix tailTrace_485881
  have hstable : (prefixWord ++ tailWord_485881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485881).length < 2 ^ (prefixWord ++ tailWord_485881).sum := by decide
  have hdescent : baseEnd_485881 < baseStart_485881 := by decide
  rcases family_descends (prefixWord ++ tailWord_485881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485898 : List Nat := [3, 1, 2, 2, 2, 1, 2, 4, 3]
def baseStart_485898 : Nat := 118140960795 + 485898 * 2 ^ 59
def prefixEnd_485898 : Nat := 4983230072969 + 3 ^ 40 * 485898 * 2
def baseEnd_485898 : Nat := 221777087163062360480357

theorem tailTrace_485898 : CollatzResearch.WordTrace tailWord_485898 prefixEnd_485898 221777087163062360480357 := by
  unfold tailWord_485898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4430538998420501404188587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11814770662454670411169565 4430538998420501404188587)
  ·
    refine ⟨6645808497630752106282881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4430538998420501404188587 6645808497630752106282881)
    ·
      refine ⟨4984356373223064079712161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6645808497630752106282881 4984356373223064079712161)
      ·
        refine ⟨3738267279917298059784121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4984356373223064079712161 3738267279917298059784121)
        ·
          refine ⟨2803700459937973544838091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3738267279917298059784121 2803700459937973544838091)
          ·
            refine ⟨4205550689906960317257137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2803700459937973544838091 4205550689906960317257137)
            ·
              refine ⟨3154163017430220237942853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4205550689906960317257137 3154163017430220237942853)
              ·
                refine ⟨591405565768166294614285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3154163017430220237942853 591405565768166294614285)
                ·
                  refine ⟨221777087163062360480357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591405565768166294614285 221777087163062360480357)
                  ·
                    rfl

theorem cell20_485898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_485898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485898 prefixEnd_485898 := by exact prefixLift 485898
  have htrace : WordTrace (prefixWord ++ tailWord_485898) baseStart_485898 baseEnd_485898 := by
    simpa [prefixWord, tailWord_485898, baseEnd_485898] using wordTrace_append hprefix tailTrace_485898
  have hstable : (prefixWord ++ tailWord_485898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485898).length < 2 ^ (prefixWord ++ tailWord_485898).sum := by decide
  have hdescent : baseEnd_485898 < baseStart_485898 := by decide
  rcases family_descends (prefixWord ++ tailWord_485898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485908 : List Nat := [2, 4, 3, 1, 1, 2, 2, 5]
def baseStart_485908 : Nat := 118140960795 + 485908 * 2 ^ 59
def prefixEnd_485908 : Nat := 4983230072969 + 3 ^ 40 * 485908 * 2
def baseEnd_485908 : Nat := 73927217145182256715661

theorem tailTrace_485908 : CollatzResearch.WordTrace tailWord_485908 prefixEnd_485908 73927217145182256715661 := by
  unfold tailWord_485908
  simp only [CollatzResearch.WordTrace]
  refine ⟨8861260361822888662309189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11815013815763851549745585 8861260361822888662309189)
  ·
    refine ⟨1661486317841791624182973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8861260361822888662309189 1661486317841791624182973)
    ·
      refine ⟨623057369190671859068615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1661486317841791624182973 623057369190671859068615)
      ·
        refine ⟨934586053786007788602923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623057369190671859068615 934586053786007788602923)
        ·
          refine ⟨1401879080679011682904385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934586053786007788602923 1401879080679011682904385)
          ·
            refine ⟨1051409310509258762178289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1401879080679011682904385 1051409310509258762178289)
            ·
              refine ⟨788556982881944071633717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051409310509258762178289 788556982881944071633717)
              ·
                refine ⟨73927217145182256715661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 788556982881944071633717 73927217145182256715661)
                ·
                  rfl

theorem cell20_485908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_485908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485908 prefixEnd_485908 := by exact prefixLift 485908
  have htrace : WordTrace (prefixWord ++ tailWord_485908) baseStart_485908 baseEnd_485908 := by
    simpa [prefixWord, tailWord_485908, baseEnd_485908] using wordTrace_append hprefix tailTrace_485908
  have hstable : (prefixWord ++ tailWord_485908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485908).length < 2 ^ (prefixWord ++ tailWord_485908).sum := by decide
  have hdescent : baseEnd_485908 < baseStart_485908 := by decide
  rcases family_descends (prefixWord ++ tailWord_485908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485911 : List Nat := [1, 1, 3, 6, 1, 2, 2, 1, 3]
def baseStart_485911 : Nat := 118140960795 + 485911 * 2 ^ 59
def prefixEnd_485911 : Nat := 4983230072969 + 3 ^ 40 * 485911 * 2
def baseEnd_485911 : Nat := 221783020717292093046971

theorem tailTrace_485911 : CollatzResearch.WordTrace tailWord_485911 prefixEnd_485911 221783020717292093046971 := by
  unfold tailWord_485911
  simp only [CollatzResearch.WordTrace]
  refine ⟨17722630142634908836977587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11815086761756605891318391 17722630142634908836977587)
  ·
    refine ⟨26583945213952363255466381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17722630142634908836977587 26583945213952363255466381)
    ·
      refine ⟨9968979455232136220799893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26583945213952363255466381 9968979455232136220799893)
      ·
        refine ⟨467295911964006385349995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9968979455232136220799893 467295911964006385349995)
        ·
          refine ⟨700943867946009578024993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467295911964006385349995 700943867946009578024993)
          ·
            refine ⟨525707900959507183518745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 700943867946009578024993 525707900959507183518745)
            ·
              refine ⟨394280925719630387639059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525707900959507183518745 394280925719630387639059)
              ·
                refine ⟨591421388579445581458589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394280925719630387639059 591421388579445581458589)
                ·
                  refine ⟨221783020717292093046971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591421388579445581458589 221783020717292093046971)
                  ·
                    rfl

theorem cell20_485911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 3].length) (baseStart_485911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485911 prefixEnd_485911 := by exact prefixLift 485911
  have htrace : WordTrace (prefixWord ++ tailWord_485911) baseStart_485911 baseEnd_485911 := by
    simpa [prefixWord, tailWord_485911, baseEnd_485911] using wordTrace_append hprefix tailTrace_485911
  have hstable : (prefixWord ++ tailWord_485911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485911).length < 2 ^ (prefixWord ++ tailWord_485911).sum := by decide
  have hdescent : baseEnd_485911 < baseStart_485911 := by decide
  rcases family_descends (prefixWord ++ tailWord_485911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485912 : List Nat := [2, 1, 2, 3, 3, 1, 1, 7]
def baseStart_485912 : Nat := 118140960795 + 485912 * 2 ^ 59
def prefixEnd_485912 : Nat := 4983230072969 + 3 ^ 40 * 485912 * 2
def baseEnd_485912 : Nat := 73927825714846844671211

theorem tailTrace_485912 : CollatzResearch.WordTrace tailWord_485912 prefixEnd_485912 73927825714846844671211 := by
  unfold tailWord_485912
  simp only [CollatzResearch.WordTrace]
  refine ⟨8861333307815643003881995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11815111077087524005175993 8861333307815643003881995)
  ·
    refine ⟨13291999961723464505822993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8861333307815643003881995 13291999961723464505822993)
    ·
      refine ⟨9968999971292598379367245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13291999961723464505822993 9968999971292598379367245)
      ·
        refine ⟨3738374989234724392262717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9968999971292598379367245 3738374989234724392262717)
        ·
          refine ⟨1401890620963021647098519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3738374989234724392262717 1401890620963021647098519)
          ·
            refine ⟨2102835931444532470647779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401890620963021647098519 2102835931444532470647779)
            ·
              refine ⟨3154253897166798705971669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2102835931444532470647779 3154253897166798705971669)
              ·
                refine ⟨73927825714846844671211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3154253897166798705971669 73927825714846844671211)
                ·
                  rfl

theorem cell20_485912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_485912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485912 prefixEnd_485912 := by exact prefixLift 485912
  have htrace : WordTrace (prefixWord ++ tailWord_485912) baseStart_485912 baseEnd_485912 := by
    simpa [prefixWord, tailWord_485912, baseEnd_485912] using wordTrace_append hprefix tailTrace_485912
  have hstable : (prefixWord ++ tailWord_485912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485912).length < 2 ^ (prefixWord ++ tailWord_485912).sum := by decide
  have hdescent : baseEnd_485912 < baseStart_485912 := by decide
  rcases family_descends (prefixWord ++ tailWord_485912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485953 : List Nat := [1, 2, 5, 1, 1, 3, 2, 2, 3]
def baseStart_485953 : Nat := 118140960795 + 485953 * 2 ^ 59
def prefixEnd_485953 : Nat := 4983230072969 + 3 ^ 40 * 485953 * 2
def baseEnd_485953 : Nat := 221802190661726613646799

theorem tailTrace_485953 : CollatzResearch.WordTrace tailWord_485953 prefixEnd_485953 221802190661726613646799 := by
  unfold tailWord_485953
  simp only [CollatzResearch.WordTrace]
  refine ⟨17724162008482750010006513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11816108005655166673337675 17724162008482750010006513)
  ·
    refine ⟨13293121506362062507504885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17724162008482750010006513 13293121506362062507504885)
    ·
      refine ⟨1246230141221443360078583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13293121506362062507504885 1246230141221443360078583)
      ·
        refine ⟨1869345211832165040117875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246230141221443360078583 1869345211832165040117875)
        ·
          refine ⟨2804017817748247560176813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869345211832165040117875 2804017817748247560176813)
          ·
            refine ⟨1051506681655592835066305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2804017817748247560176813 1051506681655592835066305)
            ·
              refine ⟨788630011241694626299729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051506681655592835066305 788630011241694626299729)
              ·
                refine ⟨591472508431270969724797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788630011241694626299729 591472508431270969724797)
                ·
                  refine ⟨221802190661726613646799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591472508431270969724797 221802190661726613646799)
                  ·
                    rfl

theorem cell20_485953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_485953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_485953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_485953 prefixEnd_485953 := by exact prefixLift 485953
  have htrace : WordTrace (prefixWord ++ tailWord_485953) baseStart_485953 baseEnd_485953 := by
    simpa [prefixWord, tailWord_485953, baseEnd_485953] using wordTrace_append hprefix tailTrace_485953
  have hstable : (prefixWord ++ tailWord_485953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485953).length < 2 ^ (prefixWord ++ tailWord_485953).sum := by decide
  have hdescent : baseEnd_485953 < baseStart_485953 := by decide
  rcases family_descends (prefixWord ++ tailWord_485953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486005 : List Nat := [1, 3, 4, 2, 2, 1, 7]
def baseStart_486005 : Nat := 118140960795 + 486005 * 2 ^ 59
def prefixEnd_486005 : Nat := 4983230072969 + 3 ^ 40 * 486005 * 2
def baseEnd_486005 : Nat := 24647324986516171545917

theorem tailTrace_486005 : CollatzResearch.WordTrace tailWord_486005 prefixEnd_486005 24647324986516171545917 := by
  unfold tailWord_486005
  simp only [CollatzResearch.WordTrace]
  refine ⟨17726058604294362890899469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11817372402862908593932979 17726058604294362890899469)
  ·
    refine ⟨6647271976610386084087301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17726058604294362890899469 6647271976610386084087301)
    ·
      refine ⟨1246363495614447390766369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6647271976610386084087301 1246363495614447390766369)
      ·
        refine ⟨934772621710835543074777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1246363495614447390766369 934772621710835543074777)
        ·
          refine ⟨701079466283126657306083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 934772621710835543074777 701079466283126657306083)
          ·
            refine ⟨1051619199424689985959125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701079466283126657306083 1051619199424689985959125)
            ·
              refine ⟨24647324986516171545917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1051619199424689985959125 24647324986516171545917)
              ·
                rfl

theorem cell20_486005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 7].length) (baseStart_486005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486005 prefixEnd_486005 := by exact prefixLift 486005
  have htrace : WordTrace (prefixWord ++ tailWord_486005) baseStart_486005 baseEnd_486005 := by
    simpa [prefixWord, tailWord_486005, baseEnd_486005] using wordTrace_append hprefix tailTrace_486005
  have hstable : (prefixWord ++ tailWord_486005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486005).length < 2 ^ (prefixWord ++ tailWord_486005).sum := by decide
  have hdescent : baseEnd_486005 < baseStart_486005 := by decide
  rcases family_descends (prefixWord ++ tailWord_486005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486012 : List Nat := [2, 2, 2, 1, 1, 2, 5, 2, 3]
def baseStart_486012 : Nat := 118140960795 + 486012 * 2 ^ 59
def prefixEnd_486012 : Nat := 4983230072969 + 3 ^ 40 * 486012 * 2
def baseEnd_486012 : Nat := 221829119869384630679891

theorem tailTrace_486012 : CollatzResearch.WordTrace tailWord_486012 prefixEnd_486012 221829119869384630679891 := by
  unfold tailWord_486012
  simp only [CollatzResearch.WordTrace]
  refine ⟨8863156957634501543202145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11817542610179335390936193 8863156957634501543202145)
  ·
    refine ⟨6647367718225876157401609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8863156957634501543202145 6647367718225876157401609)
    ·
      refine ⟨4985525788669407118051207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6647367718225876157401609 4985525788669407118051207)
      ·
        refine ⟨7478288683004110677076811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4985525788669407118051207 7478288683004110677076811)
        ·
          refine ⟨11217433024506166015615217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7478288683004110677076811 11217433024506166015615217)
          ·
            refine ⟨8413074768379624511711413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11217433024506166015615217 8413074768379624511711413)
            ·
              refine ⟨788725759535589797972945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8413074768379624511711413 788725759535589797972945)
              ·
                refine ⟨591544319651692348479709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788725759535589797972945 591544319651692348479709)
                ·
                  refine ⟨221829119869384630679891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591544319651692348479709 221829119869384630679891)
                  ·
                    rfl

theorem cell20_486012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_486012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486012 prefixEnd_486012 := by exact prefixLift 486012
  have htrace : WordTrace (prefixWord ++ tailWord_486012) baseStart_486012 baseEnd_486012 := by
    simpa [prefixWord, tailWord_486012, baseEnd_486012] using wordTrace_append hprefix tailTrace_486012
  have hstable : (prefixWord ++ tailWord_486012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486012).length < 2 ^ (prefixWord ++ tailWord_486012).sum := by decide
  have hdescent : baseEnd_486012 < baseStart_486012 := by decide
  rcases family_descends (prefixWord ++ tailWord_486012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486036 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 4]
def baseStart_486036 : Nat := 118140960795 + 486036 * 2 ^ 59
def prefixEnd_486036 : Nat := 4983230072969 + 3 ^ 40 * 486036 * 2
def baseEnd_486036 : Nat := 221840074123347213879793

theorem tailTrace_486036 : CollatzResearch.WordTrace tailWord_486036 prefixEnd_486036 221840074123347213879793 := by
  unfold tailWord_486036
  simp only [CollatzResearch.WordTrace]
  refine ⟨8863594633591027592638981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11818126178121370123518641 8863594633591027592638981)
  ·
    refine ⟨1661923993798317673619809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8863594633591027592638981 1661923993798317673619809)
    ·
      refine ⟨1246442995348738255214857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1661923993798317673619809 1246442995348738255214857)
      ·
        refine ⟨934832246511553691411143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1246442995348738255214857 934832246511553691411143)
        ·
          refine ⟨1402248369767330537116715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934832246511553691411143 1402248369767330537116715)
          ·
            refine ⟨2103372554650995805675073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402248369767330537116715 2103372554650995805675073)
            ·
              refine ⟨1577529415988246854256305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2103372554650995805675073 1577529415988246854256305)
              ·
                refine ⟨1183147061991185140692229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1577529415988246854256305 1183147061991185140692229)
                ·
                  refine ⟨221840074123347213879793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1183147061991185140692229 221840074123347213879793)
                  ·
                    rfl

theorem cell20_486036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_486036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486036 prefixEnd_486036 := by exact prefixLift 486036
  have htrace : WordTrace (prefixWord ++ tailWord_486036) baseStart_486036 baseEnd_486036 := by
    simpa [prefixWord, tailWord_486036, baseEnd_486036] using wordTrace_append hprefix tailTrace_486036
  have hstable : (prefixWord ++ tailWord_486036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486036).length < 2 ^ (prefixWord ++ tailWord_486036).sum := by decide
  have hdescent : baseEnd_486036 < baseStart_486036 := by decide
  rcases family_descends (prefixWord ++ tailWord_486036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486070 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_486070 : Nat := 118140960795 + 486070 * 2 ^ 59
def prefixEnd_486070 : Nat := 4983230072969 + 3 ^ 40 * 486070 * 2
def baseEnd_486070 : Nat := 221855592649794206746321

theorem tailTrace_486070 : CollatzResearch.WordTrace tailWord_486070 prefixEnd_486070 221855592649794206746321 := by
  unfold tailWord_486070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1108026834316179937000979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11818952899372585994677109 1108026834316179937000979)
  ·
    refine ⟨1662040251474269905501469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1108026834316179937000979 1662040251474269905501469)
    ·
      refine ⟨623265094302851214563051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1662040251474269905501469 623265094302851214563051)
      ·
        refine ⟨934897641454276821844577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623265094302851214563051 934897641454276821844577)
        ·
          refine ⟨701173231090707616383433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 934897641454276821844577 701173231090707616383433)
          ·
            refine ⟨525879923318030712287575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701173231090707616383433 525879923318030712287575)
            ·
              refine ⟨788819884977046068431363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525879923318030712287575 788819884977046068431363)
              ·
                refine ⟨1183229827465569102647045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788819884977046068431363 1183229827465569102647045)
                ·
                  refine ⟨221855592649794206746321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1183229827465569102647045 221855592649794206746321)
                  ·
                    rfl

theorem cell20_486070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_486070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486070 prefixEnd_486070 := by exact prefixLift 486070
  have htrace : WordTrace (prefixWord ++ tailWord_486070) baseStart_486070 baseEnd_486070 := by
    simpa [prefixWord, tailWord_486070, baseEnd_486070] using wordTrace_append hprefix tailTrace_486070
  have hstable : (prefixWord ++ tailWord_486070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486070).length < 2 ^ (prefixWord ++ tailWord_486070).sum := by decide
  have hdescent : baseEnd_486070 < baseStart_486070 := by decide
  rcases family_descends (prefixWord ++ tailWord_486070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486084 : List Nat := [2, 3, 3, 1, 1, 4, 2, 1, 3]
def baseStart_486084 : Nat := 118140960795 + 486084 * 2 ^ 59
def prefixEnd_486084 : Nat := 4983230072969 + 3 ^ 40 * 486084 * 2
def baseEnd_486084 : Nat := 221861982631272380279597

theorem tailTrace_486084 : CollatzResearch.WordTrace tailWord_486084 prefixEnd_486084 221861982631272380279597 := by
  unfold tailWord_486084
  simp only [CollatzResearch.WordTrace]
  refine ⟨8864469985504079691512653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11819293314005439588683537 8864469985504079691512653)
  ·
    refine ⟨3324176244564029884317245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8864469985504079691512653 3324176244564029884317245)
    ·
      refine ⟨1246566091711511206618967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3324176244564029884317245 1246566091711511206618967)
      ·
        refine ⟨1869849137567266809928451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246566091711511206618967 1869849137567266809928451)
        ·
          refine ⟨2804773706350900214892677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869849137567266809928451 2804773706350900214892677)
          ·
            refine ⟨525895069940793790292377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2804773706350900214892677 525895069940793790292377)
            ·
              refine ⟨394421302455595342719283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525895069940793790292377 394421302455595342719283)
              ·
                refine ⟨591631953683393014078925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394421302455595342719283 591631953683393014078925)
                ·
                  refine ⟨221861982631272380279597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591631953683393014078925 221861982631272380279597)
                  ·
                    rfl

theorem cell20_486084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_486084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486084 prefixEnd_486084 := by exact prefixLift 486084
  have htrace : WordTrace (prefixWord ++ tailWord_486084) baseStart_486084 baseEnd_486084 := by
    simpa [prefixWord, tailWord_486084, baseEnd_486084] using wordTrace_append hprefix tailTrace_486084
  have hstable : (prefixWord ++ tailWord_486084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486084).length < 2 ^ (prefixWord ++ tailWord_486084).sum := by decide
  have hdescent : baseEnd_486084 < baseStart_486084 := by decide
  rcases family_descends (prefixWord ++ tailWord_486084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486088 : List Nat := [2, 1, 3, 1, 2, 4, 1, 3, 3]
def baseStart_486088 : Nat := 118140960795 + 486088 * 2 ^ 59
def prefixEnd_486088 : Nat := 4983230072969 + 3 ^ 40 * 486088 * 2
def baseEnd_486088 : Nat := 221863808340266144146247

theorem tailTrace_486088 : CollatzResearch.WordTrace tailWord_486088 prefixEnd_486088 221863808340266144146247 := by
  unfold tailWord_486088
  simp only [CollatzResearch.WordTrace]
  refine ⟨8864542931496834033085459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11819390575329112044113945 8864542931496834033085459)
  ·
    refine ⟨13296814397245251049628189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8864542931496834033085459 13296814397245251049628189)
    ·
      refine ⟨4986305398966969143610571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13296814397245251049628189 4986305398966969143610571)
      ·
        refine ⟨7479458098450453715415857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4986305398966969143610571 7479458098450453715415857)
        ·
          refine ⟨5609593573837840286561893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7479458098450453715415857 5609593573837840286561893)
          ·
            refine ⟨1051798795094595053730355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5609593573837840286561893 1051798795094595053730355)
            ·
              refine ⟨1577698192641892580595533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051798795094595053730355 1577698192641892580595533)
              ·
                refine ⟨591636822240709717723325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1577698192641892580595533 591636822240709717723325)
                ·
                  refine ⟨221863808340266144146247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591636822240709717723325 221863808340266144146247)
                  ·
                    rfl

theorem cell20_486088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_486088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486088 prefixEnd_486088 := by exact prefixLift 486088
  have htrace : WordTrace (prefixWord ++ tailWord_486088) baseStart_486088 baseEnd_486088 := by
    simpa [prefixWord, tailWord_486088, baseEnd_486088] using wordTrace_append hprefix tailTrace_486088
  have hstable : (prefixWord ++ tailWord_486088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486088).length < 2 ^ (prefixWord ++ tailWord_486088).sum := by decide
  have hdescent : baseEnd_486088 < baseStart_486088 := by decide
  rcases family_descends (prefixWord ++ tailWord_486088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486126 : List Nat := [4, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_486126 : Nat := 118140960795 + 486126 * 2 ^ 59
def prefixEnd_486126 : Nat := 4983230072969 + 3 ^ 40 * 486126 * 2
def baseEnd_486126 : Nat := 221881152575706900879425

theorem tailTrace_486126 : CollatzResearch.WordTrace tailWord_486126 prefixEnd_486126 221881152575706900879425 := by
  unfold tailWord_486126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2216308979607000069506779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11820314557904000370702821 2216308979607000069506779)
  ·
    refine ⟨3324463469410500104260169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2216308979607000069506779 3324463469410500104260169)
    ·
      refine ⟨2493347602057875078195127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3324463469410500104260169 2493347602057875078195127)
      ·
        refine ⟨3740021403086812617292691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2493347602057875078195127 3740021403086812617292691)
        ·
          refine ⟨5610032104630218925939037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3740021403086812617292691 5610032104630218925939037)
          ·
            refine ⟨2103762039236332097227139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5610032104630218925939037 2103762039236332097227139)
            ·
              refine ⟨3155643058854498145840709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2103762039236332097227139 3155643058854498145840709)
              ·
                refine ⟨591683073535218402345133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3155643058854498145840709 591683073535218402345133)
                ·
                  refine ⟨221881152575706900879425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591683073535218402345133 221881152575706900879425)
                  ·
                    rfl

theorem cell20_486126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_486126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486126 prefixEnd_486126 := by exact prefixLift 486126
  have htrace : WordTrace (prefixWord ++ tailWord_486126) baseStart_486126 baseEnd_486126 := by
    simpa [prefixWord, tailWord_486126, baseEnd_486126] using wordTrace_append hprefix tailTrace_486126
  have hstable : (prefixWord ++ tailWord_486126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486126).length < 2 ^ (prefixWord ++ tailWord_486126).sum := by decide
  have hdescent : baseEnd_486126 < baseStart_486126 := by decide
  rcases family_descends (prefixWord ++ tailWord_486126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486132 : List Nat := [2, 6, 1, 1, 3, 1, 1, 5]
def baseStart_486132 : Nat := 118140960795 + 486132 * 2 ^ 59
def prefixEnd_486132 : Nat := 4983230072969 + 3 ^ 40 * 486132 * 2
def baseEnd_486132 : Nat := 73961297046399182226467

theorem tailTrace_486132 : CollatzResearch.WordTrace tailWord_486132 prefixEnd_486132 73961297046399182226467 := by
  unfold tailWord_486132
  simp only [CollatzResearch.WordTrace]
  refine ⟨8865345337417131790386325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11820460449889509053848433 8865345337417131790386325)
  ·
    refine ⟨415563062691428052674359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8865345337417131790386325 415563062691428052674359)
    ·
      refine ⟨623344594037142079011539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415563062691428052674359 623344594037142079011539)
      ·
        refine ⟨935016891055713118517309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623344594037142079011539 935016891055713118517309)
        ·
          refine ⟨350631334145892419443991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 935016891055713118517309 350631334145892419443991)
          ·
            refine ⟨525947001218838629165987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350631334145892419443991 525947001218838629165987)
            ·
              refine ⟨788920501828257943748981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525947001218838629165987 788920501828257943748981)
              ·
                refine ⟨73961297046399182226467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 788920501828257943748981 73961297046399182226467)
                ·
                  rfl

theorem cell20_486132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 5].length) (baseStart_486132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486132 prefixEnd_486132 := by exact prefixLift 486132
  have htrace : WordTrace (prefixWord ++ tailWord_486132) baseStart_486132 baseEnd_486132 := by
    simpa [prefixWord, tailWord_486132, baseEnd_486132] using wordTrace_append hprefix tailTrace_486132
  have hstable : (prefixWord ++ tailWord_486132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486132).length < 2 ^ (prefixWord ++ tailWord_486132).sum := by decide
  have hdescent : baseEnd_486132 < baseStart_486132 := by decide
  rcases family_descends (prefixWord ++ tailWord_486132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486140 : List Nat := [2, 2, 2, 1, 3, 2, 3, 5]
def baseStart_486140 : Nat := 118140960795 + 486140 * 2 ^ 59
def prefixEnd_486140 : Nat := 4983230072969 + 3 ^ 40 * 486140 * 2
def baseEnd_486140 : Nat := 73962514185728358137567

theorem tailTrace_486140 : CollatzResearch.WordTrace tailWord_486140 prefixEnd_486140 73962514185728358137567 := by
  unfold tailWord_486140
  simp only [CollatzResearch.WordTrace]
  refine ⟨8865491229402640473531937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11820654972536853964709249 8865491229402640473531937)
  ·
    refine ⟨6649118422051980355148953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8865491229402640473531937 6649118422051980355148953)
    ·
      refine ⟨4986838816538985266361715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6649118422051980355148953 4986838816538985266361715)
      ·
        refine ⟨7480258224808477899542573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4986838816538985266361715 7480258224808477899542573)
        ·
          refine ⟨2805096834303179212328465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7480258224808477899542573 2805096834303179212328465)
          ·
            refine ⟨2103822625727384409246349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2805096834303179212328465 2103822625727384409246349)
            ·
              refine ⟨788933484647769153467381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2103822625727384409246349 788933484647769153467381)
              ·
                refine ⟨73962514185728358137567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 788933484647769153467381 73962514185728358137567)
                ·
                  rfl

theorem cell20_486140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_486140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486140 prefixEnd_486140 := by exact prefixLift 486140
  have htrace : WordTrace (prefixWord ++ tailWord_486140) baseStart_486140 baseEnd_486140 := by
    simpa [prefixWord, tailWord_486140, baseEnd_486140] using wordTrace_append hprefix tailTrace_486140
  have hstable : (prefixWord ++ tailWord_486140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486140).length < 2 ^ (prefixWord ++ tailWord_486140).sum := by decide
  have hdescent : baseEnd_486140 < baseStart_486140 := by decide
  rcases family_descends (prefixWord ++ tailWord_486140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486161 : List Nat := [1, 2, 2, 1, 1, 3, 2, 8]
def baseStart_486161 : Nat := 118140960795 + 486161 * 2 ^ 59
def prefixEnd_486161 : Nat := 4983230072969 + 3 ^ 40 * 486161 * 2
def baseEnd_486161 : Nat := 73965709176467444904205

theorem tailTrace_486161 : CollatzResearch.WordTrace tailWord_486161 prefixEnd_486161 73965709176467444904205 := by
  unfold tailWord_486161
  simp only [CollatzResearch.WordTrace]
  refine ⟨17731748391729201533578337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11821165594486134355718891 17731748391729201533578337)
  ·
    refine ⟨13298811293796901150183753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17731748391729201533578337 13298811293796901150183753)
    ·
      refine ⟨9974108470347675862637815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13298811293796901150183753 9974108470347675862637815)
      ·
        refine ⟨14961162705521513793956723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9974108470347675862637815 14961162705521513793956723)
        ·
          refine ⟨22441744058282270690935085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14961162705521513793956723 22441744058282270690935085)
          ·
            refine ⟨8415654021855851509100657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22441744058282270690935085 8415654021855851509100657)
            ·
              refine ⟨6311740516391888631825493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8415654021855851509100657 6311740516391888631825493)
              ·
                refine ⟨73965709176467444904205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6311740516391888631825493 73965709176467444904205)
                ·
                  rfl

theorem cell20_486161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 8].length) (baseStart_486161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486161 prefixEnd_486161 := by exact prefixLift 486161
  have htrace : WordTrace (prefixWord ++ tailWord_486161) baseStart_486161 baseEnd_486161 := by
    simpa [prefixWord, tailWord_486161, baseEnd_486161] using wordTrace_append hprefix tailTrace_486161
  have hstable : (prefixWord ++ tailWord_486161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486161).length < 2 ^ (prefixWord ++ tailWord_486161).sum := by decide
  have hdescent : baseEnd_486161 < baseStart_486161 := by decide
  rcases family_descends (prefixWord ++ tailWord_486161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486167 : List Nat := [1, 1, 3, 4, 3, 1, 2, 3, 2]
def baseStart_486167 : Nat := 118140960795 + 486167 * 2 ^ 59
def prefixEnd_486167 : Nat := 4983230072969 + 3 ^ 40 * 486167 * 2
def baseEnd_486167 : Nat := 221899866092892980512591

theorem tailTrace_486167 : CollatzResearch.WordTrace tailWord_486167 prefixEnd_486167 221899866092892980512591 := by
  unfold tailWord_486167
  simp only [CollatzResearch.WordTrace]
  refine ⟨17731967229707464558296755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11821311486471643038864503 17731967229707464558296755)
  ·
    refine ⟨26597950844561196837445133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17731967229707464558296755 26597950844561196837445133)
    ·
      refine ⟨9974231566710448814041925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26597950844561196837445133 9974231566710448814041925)
      ·
        refine ⟨1870168418758209152632861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9974231566710448814041925 1870168418758209152632861)
        ·
          refine ⟨701313157034328432237323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1870168418758209152632861 701313157034328432237323)
          ·
            refine ⟨1051969735551492648355985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701313157034328432237323 1051969735551492648355985)
            ·
              refine ⟨788977301663619486266989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051969735551492648355985 788977301663619486266989)
              ·
                refine ⟨295866488123857307350121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 788977301663619486266989 295866488123857307350121)
                ·
                  refine ⟨221899866092892980512591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295866488123857307350121 221899866092892980512591)
                  ·
                    rfl

theorem cell20_486167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 2].length) (baseStart_486167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486167 prefixEnd_486167 := by exact prefixLift 486167
  have htrace : WordTrace (prefixWord ++ tailWord_486167) baseStart_486167 baseEnd_486167 := by
    simpa [prefixWord, tailWord_486167, baseEnd_486167] using wordTrace_append hprefix tailTrace_486167
  have hstable : (prefixWord ++ tailWord_486167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486167).length < 2 ^ (prefixWord ++ tailWord_486167).sum := by decide
  have hdescent : baseEnd_486167 < baseStart_486167 := by decide
  rcases family_descends (prefixWord ++ tailWord_486167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486178 : List Nat := [3, 3, 1, 1, 2, 3, 7]
def baseStart_486178 : Nat := 118140960795 + 486178 * 2 ^ 59
def prefixEnd_486178 : Nat := 4983230072969 + 3 ^ 40 * 486178 * 2
def baseEnd_486178 : Nat := 24656098532513981238431

theorem tailTrace_486178 : CollatzResearch.WordTrace tailWord_486178 prefixEnd_486178 24656098532513981238431 := by
  unfold tailWord_486178
  simp only [CollatzResearch.WordTrace]
  refine ⟨4433092108166903359236797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11821578955111742291298125 4433092108166903359236797)
  ·
    refine ⟨1662409540562588759713799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4433092108166903359236797 1662409540562588759713799)
    ·
      refine ⟨2493614310843883139570699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1662409540562588759713799 2493614310843883139570699)
      ·
        refine ⟨3740421466265824709356049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2493614310843883139570699 3740421466265824709356049)
        ·
          refine ⟨2805316099699368532017037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3740421466265824709356049 2805316099699368532017037)
          ·
            refine ⟨1051993537387263199506389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2805316099699368532017037 1051993537387263199506389)
            ·
              refine ⟨24656098532513981238431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1051993537387263199506389 24656098532513981238431)
              ·
                rfl

theorem cell20_486178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 7].length) (baseStart_486178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486178 prefixEnd_486178 := by exact prefixLift 486178
  have htrace : WordTrace (prefixWord ++ tailWord_486178) baseStart_486178 baseEnd_486178 := by
    simpa [prefixWord, tailWord_486178, baseEnd_486178] using wordTrace_append hprefix tailTrace_486178
  have hstable : (prefixWord ++ tailWord_486178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486178).length < 2 ^ (prefixWord ++ tailWord_486178).sum := by decide
  have hdescent : baseEnd_486178 < baseStart_486178 := by decide
  rcases family_descends (prefixWord ++ tailWord_486178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486199 : List Nat := [1, 1, 3, 1, 2, 1, 4, 7]
def baseStart_486199 : Nat := 118140960795 + 486199 * 2 ^ 59
def prefixEnd_486199 : Nat := 4983230072969 + 3 ^ 40 * 486199 * 2
def baseEnd_486199 : Nat := 73971490588281030481931

theorem tailTrace_486199 : CollatzResearch.WordTrace tailWord_486199 prefixEnd_486199 73971490588281030481931 := by
  unfold tailWord_486199
  simp only [CollatzResearch.WordTrace]
  refine ⟨17733134365591534023461651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11822089577061022682307767 17733134365591534023461651)
  ·
    refine ⟨26599701548387301035192477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17733134365591534023461651 26599701548387301035192477)
    ·
      refine ⟨9974888080645237888197179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26599701548387301035192477 9974888080645237888197179)
      ·
        refine ⟨14962332120967856832295769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9974888080645237888197179 14962332120967856832295769)
        ·
          refine ⟨11221749090725892624221827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14962332120967856832295769 11221749090725892624221827)
          ·
            refine ⟨16832623636088838936332741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11221749090725892624221827 16832623636088838936332741)
            ·
              refine ⟨3156116931766657300562389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16832623636088838936332741 3156116931766657300562389)
              ·
                refine ⟨73971490588281030481931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3156116931766657300562389 73971490588281030481931)
                ·
                  rfl

theorem cell20_486199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 7].length) (baseStart_486199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486199 prefixEnd_486199 := by exact prefixLift 486199
  have htrace : WordTrace (prefixWord ++ tailWord_486199) baseStart_486199 baseEnd_486199 := by
    simpa [prefixWord, tailWord_486199, baseEnd_486199] using wordTrace_append hprefix tailTrace_486199
  have hstable : (prefixWord ++ tailWord_486199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486199).length < 2 ^ (prefixWord ++ tailWord_486199).sum := by decide
  have hdescent : baseEnd_486199 < baseStart_486199 := by decide
  rcases family_descends (prefixWord ++ tailWord_486199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486212 : List Nat := [2, 3, 4, 2, 1, 1, 1, 6]
def baseStart_486212 : Nat := 118140960795 + 486212 * 2 ^ 59
def prefixEnd_486212 : Nat := 4983230072969 + 3 ^ 40 * 486212 * 2
def baseEnd_486212 : Nat := 73973468439690941337469

theorem tailTrace_486212 : CollatzResearch.WordTrace tailWord_486212 prefixEnd_486212 73973468439690941337469 := by
  unfold tailWord_486212
  simp only [CollatzResearch.WordTrace]
  refine ⟨8866804257272218621842445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11822405676362958162456593 8866804257272218621842445)
  ·
    refine ⟨3325051596477081983190917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8866804257272218621842445 3325051596477081983190917)
    ·
      refine ⟨623447174339452871848297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3325051596477081983190917 623447174339452871848297)
      ·
        refine ⟨467585380754589653886223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623447174339452871848297 467585380754589653886223)
        ·
          refine ⟨701378071131884480829335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467585380754589653886223 701378071131884480829335)
          ·
            refine ⟨1052067106697826721244003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701378071131884480829335 1052067106697826721244003)
            ·
              refine ⟨1578100660046740081866005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052067106697826721244003 1578100660046740081866005)
              ·
                refine ⟨73973468439690941337469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1578100660046740081866005 73973468439690941337469)
                ·
                  rfl

theorem cell20_486212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_486212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486212 prefixEnd_486212 := by exact prefixLift 486212
  have htrace : WordTrace (prefixWord ++ tailWord_486212) baseStart_486212 baseEnd_486212 := by
    simpa [prefixWord, tailWord_486212, baseEnd_486212] using wordTrace_append hprefix tailTrace_486212
  have hstable : (prefixWord ++ tailWord_486212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486212).length < 2 ^ (prefixWord ++ tailWord_486212).sum := by decide
  have hdescent : baseEnd_486212 < baseStart_486212 := by decide
  rcases family_descends (prefixWord ++ tailWord_486212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486243 : List Nat := [1, 1, 1, 5, 3, 2, 3, 2, 2]
def baseStart_486243 : Nat := 118140960795 + 486243 * 2 ^ 59
def prefixEnd_486243 : Nat := 4983230072969 + 3 ^ 40 * 486243 * 2
def baseEnd_486243 : Nat := 221934554563774493978947

theorem tailTrace_486243 : CollatzResearch.WordTrace tailWord_486243 prefixEnd_486243 221934554563774493978947 := by
  unfold tailWord_486243
  simp only [CollatzResearch.WordTrace]
  refine ⟨17734739177432129538063383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11823159451621419692042255 17734739177432129538063383)
  ·
    refine ⟨26602108766148194307095075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17734739177432129538063383 26602108766148194307095075)
    ·
      refine ⟨39903163149222291460642613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26602108766148194307095075 39903163149222291460642613)
      ·
        refine ⟨3740921545239589824435245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39903163149222291460642613 3740921545239589824435245)
        ·
          refine ⟨1402845579464846184163217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3740921545239589824435245 1402845579464846184163217)
          ·
            refine ⟨1052134184598634638122413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1402845579464846184163217 1052134184598634638122413)
            ·
              refine ⟨394550319224487989295905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1052134184598634638122413 394550319224487989295905)
              ·
                refine ⟨295912739418365991971929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394550319224487989295905 295912739418365991971929)
                ·
                  refine ⟨221934554563774493978947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295912739418365991971929 221934554563774493978947)
                  ·
                    rfl

theorem cell20_486243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 2].length) (baseStart_486243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486243 prefixEnd_486243 := by exact prefixLift 486243
  have htrace : WordTrace (prefixWord ++ tailWord_486243) baseStart_486243 baseEnd_486243 := by
    simpa [prefixWord, tailWord_486243, baseEnd_486243] using wordTrace_append hprefix tailTrace_486243
  have hstable : (prefixWord ++ tailWord_486243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486243).length < 2 ^ (prefixWord ++ tailWord_486243).sum := by decide
  have hdescent : baseEnd_486243 < baseStart_486243 := by decide
  rcases family_descends (prefixWord ++ tailWord_486243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486247 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 4]
def baseStart_486247 : Nat := 118140960795 + 486247 * 2 ^ 59
def prefixEnd_486247 : Nat := 4983230072969 + 3 ^ 40 * 486247 * 2
def baseEnd_486247 : Nat := 221936380272768257845597

theorem tailTrace_486247 : CollatzResearch.WordTrace tailWord_486247 prefixEnd_486247 221936380272768257845597 := by
  unfold tailWord_486247
  simp only [CollatzResearch.WordTrace]
  refine ⟨17734885069417638221208995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11823256712945092147472663 17734885069417638221208995)
  ·
    refine ⟨26602327604126457331813493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17734885069417638221208995 26602327604126457331813493)
    ·
      refine ⟨2493968212886855374857515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26602327604126457331813493 2493968212886855374857515)
      ·
        refine ⟨3740952319330283062286273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2493968212886855374857515 3740952319330283062286273)
        ·
          refine ⟨2805714239497712296714705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3740952319330283062286273 2805714239497712296714705)
          ·
            refine ⟨2104285679623284222536029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2805714239497712296714705 2104285679623284222536029)
            ·
              refine ⟨789107129858731583451011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2104285679623284222536029 789107129858731583451011)
              ·
                refine ⟨1183660694788097375176517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789107129858731583451011 1183660694788097375176517)
                ·
                  refine ⟨221936380272768257845597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1183660694788097375176517 221936380272768257845597)
                  ·
                    rfl

theorem cell20_486247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 4].length) (baseStart_486247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486247 prefixEnd_486247 := by exact prefixLift 486247
  have htrace : WordTrace (prefixWord ++ tailWord_486247) baseStart_486247 baseEnd_486247 := by
    simpa [prefixWord, tailWord_486247, baseEnd_486247] using wordTrace_append hprefix tailTrace_486247
  have hstable : (prefixWord ++ tailWord_486247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486247).length < 2 ^ (prefixWord ++ tailWord_486247).sum := by decide
  have hdescent : baseEnd_486247 < baseStart_486247 := by decide
  rcases family_descends (prefixWord ++ tailWord_486247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486257 : List Nat := [1, 2, 2, 2, 1, 6, 2, 1, 3]
def baseStart_486257 : Nat := 118140960795 + 486257 * 2 ^ 59
def prefixEnd_486257 : Nat := 4983230072969 + 3 ^ 40 * 486257 * 2
def baseEnd_486257 : Nat := 221940944545252667512223

theorem tailTrace_486257 : CollatzResearch.WordTrace tailWord_486257 prefixEnd_486257 221940944545252667512223 := by
  unfold tailWord_486257
  simp only [CollatzResearch.WordTrace]
  refine ⟨17735249799381409929073025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11823499866254273286048683 17735249799381409929073025)
  ·
    refine ⟨13301437349536057446804769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17735249799381409929073025 13301437349536057446804769)
    ·
      refine ⟨9976078012152043085103577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13301437349536057446804769 9976078012152043085103577)
      ·
        refine ⟨7482058509114032313827683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9976078012152043085103577 7482058509114032313827683)
        ·
          refine ⟨11223087763671048470741525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7482058509114032313827683 11223087763671048470741525)
          ·
            refine ⟨526082238922080397066009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11223087763671048470741525 526082238922080397066009)
            ·
              refine ⟨394561679191560297799507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526082238922080397066009 394561679191560297799507)
              ·
                refine ⟨591842518787340446699261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394561679191560297799507 591842518787340446699261)
                ·
                  refine ⟨221940944545252667512223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591842518787340446699261 221940944545252667512223)
                  ·
                    rfl

theorem cell20_486257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 3].length) (baseStart_486257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486257 prefixEnd_486257 := by exact prefixLift 486257
  have htrace : WordTrace (prefixWord ++ tailWord_486257) baseStart_486257 baseEnd_486257 := by
    simpa [prefixWord, tailWord_486257, baseEnd_486257] using wordTrace_append hprefix tailTrace_486257
  have hstable : (prefixWord ++ tailWord_486257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486257).length < 2 ^ (prefixWord ++ tailWord_486257).sum := by decide
  have hdescent : baseEnd_486257 < baseStart_486257 := by decide
  rcases family_descends (prefixWord ++ tailWord_486257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486268 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 4]
def baseStart_486268 : Nat := 118140960795 + 486268 * 2 ^ 59
def prefixEnd_486268 : Nat := 4983230072969 + 3 ^ 40 * 486268 * 2
def baseEnd_486268 : Nat := 221945965244985518145511

theorem tailTrace_486268 : CollatzResearch.WordTrace tailWord_486268 prefixEnd_486268 221945965244985518145511 := by
  unfold tailWord_486268
  simp only [CollatzResearch.WordTrace]
  refine ⟨8867825501170779403861729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11823767334894372538482305 8867825501170779403861729)
  ·
    refine ⟨6650869125878084552896297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8867825501170779403861729 6650869125878084552896297)
    ·
      refine ⟨4988151844408563414672223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6650869125878084552896297 4988151844408563414672223)
      ·
        refine ⟨7482227766612845122008335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4988151844408563414672223 7482227766612845122008335)
        ·
          refine ⟨11223341649919267683012503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7482227766612845122008335 11223341649919267683012503)
          ·
            refine ⟨16835012474878901524518755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11223341649919267683012503 16835012474878901524518755)
            ·
              refine ⟨25252518712318352286778133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16835012474878901524518755 25252518712318352286778133)
              ·
                refine ⟨1183711814639922763442725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25252518712318352286778133 1183711814639922763442725)
                ·
                  refine ⟨221945965244985518145511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1183711814639922763442725 221945965244985518145511)
                  ·
                    rfl

theorem cell20_486268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_486268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486268 prefixEnd_486268 := by exact prefixLift 486268
  have htrace : WordTrace (prefixWord ++ tailWord_486268) baseStart_486268 baseEnd_486268 := by
    simpa [prefixWord, tailWord_486268, baseEnd_486268] using wordTrace_append hprefix tailTrace_486268
  have hstable : (prefixWord ++ tailWord_486268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486268).length < 2 ^ (prefixWord ++ tailWord_486268).sum := by decide
  have hdescent : baseEnd_486268 < baseStart_486268 := by decide
  rcases family_descends (prefixWord ++ tailWord_486268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486275 : List Nat := [1, 1, 1, 3, 4, 1, 1, 8]
def baseStart_486275 : Nat := 118140960795 + 486275 * 2 ^ 59
def prefixEnd_486275 : Nat := 4983230072969 + 3 ^ 40 * 486275 * 2
def baseEnd_486275 : Nat := 73983053411908201637383

theorem tailTrace_486275 : CollatzResearch.WordTrace tailWord_486275 prefixEnd_486275 73983053411908201637383 := by
  unfold tailWord_486275
  simp only [CollatzResearch.WordTrace]
  refine ⟨17735906313316199003228279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11823937542210799335485519 17735906313316199003228279)
  ·
    refine ⟨26603859469974298504842419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17735906313316199003228279 26603859469974298504842419)
    ·
      refine ⟨39905789204961447757263629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26603859469974298504842419 39905789204961447757263629)
      ·
        refine ⟨14964670951860542908973861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39905789204961447757263629 14964670951860542908973861)
        ·
          refine ⟨2805875803473851795432599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14964670951860542908973861 2805875803473851795432599)
          ·
            refine ⟨4208813705210777693148899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2805875803473851795432599 4208813705210777693148899)
            ·
              refine ⟨6313220557816166539723349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4208813705210777693148899 6313220557816166539723349)
              ·
                refine ⟨73983053411908201637383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6313220557816166539723349 73983053411908201637383)
                ·
                  rfl

theorem cell20_486275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 8].length) (baseStart_486275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486275 prefixEnd_486275 := by exact prefixLift 486275
  have htrace : WordTrace (prefixWord ++ tailWord_486275) baseStart_486275 baseEnd_486275 := by
    simpa [prefixWord, tailWord_486275, baseEnd_486275] using wordTrace_append hprefix tailTrace_486275
  have hstable : (prefixWord ++ tailWord_486275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486275).length < 2 ^ (prefixWord ++ tailWord_486275).sum := by decide
  have hdescent : baseEnd_486275 < baseStart_486275 := by decide
  rcases family_descends (prefixWord ++ tailWord_486275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486294 : List Nat := [5, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_486294 : Nat := 118140960795 + 486294 * 2 ^ 59
def prefixEnd_486294 : Nat := 4983230072969 + 3 ^ 40 * 486294 * 2
def baseEnd_486294 : Nat := 221957832353444983278739

theorem tailTrace_486294 : CollatzResearch.WordTrace tailWord_486294 prefixEnd_486294 221957832353444983278739 := by
  unfold tailWord_486294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1108537456265460328010621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11824399533498243498779957 1108537456265460328010621)
  ·
    refine ⟨415701546099547623003983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1108537456265460328010621 415701546099547623003983)
    ·
      refine ⟨623552319149321434505975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415701546099547623003983 623552319149321434505975)
      ·
        refine ⟨935328478723982151758963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623552319149321434505975 935328478723982151758963)
        ·
          refine ⟨1402992718085973227638445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935328478723982151758963 1402992718085973227638445)
          ·
            refine ⟨526122269282239960364417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1402992718085973227638445 526122269282239960364417)
            ·
              refine ⟨394591701961679970273313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526122269282239960364417 394591701961679970273313)
              ·
                refine ⟨295943776471259977704985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394591701961679970273313 295943776471259977704985)
                ·
                  refine ⟨221957832353444983278739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295943776471259977704985 221957832353444983278739)
                  ·
                    rfl

theorem cell20_486294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_486294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486294 prefixEnd_486294 := by exact prefixLift 486294
  have htrace : WordTrace (prefixWord ++ tailWord_486294) baseStart_486294 baseEnd_486294 := by
    simpa [prefixWord, tailWord_486294, baseEnd_486294] using wordTrace_append hprefix tailTrace_486294
  have hstable : (prefixWord ++ tailWord_486294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486294).length < 2 ^ (prefixWord ++ tailWord_486294).sum := by decide
  have hdescent : baseEnd_486294 < baseStart_486294 := by decide
  rcases family_descends (prefixWord ++ tailWord_486294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486298 : List Nat := [3, 1, 1, 4, 3, 2, 2, 2, 2]
def baseStart_486298 : Nat := 118140960795 + 486298 * 2 ^ 59
def prefixEnd_486298 : Nat := 4983230072969 + 3 ^ 40 * 486298 * 2
def baseEnd_486298 : Nat := 221959658062438747145389

theorem tailTrace_486298 : CollatzResearch.WordTrace tailWord_486298 prefixEnd_486298 221959658062438747145389 := by
  unfold tailWord_486298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4434186298058218482828887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11824496794821915954210365 4434186298058218482828887)
  ·
    refine ⟨6651279447087327724243331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4434186298058218482828887 6651279447087327724243331)
    ·
      refine ⟨9976919170630991586364997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6651279447087327724243331 9976919170630991586364997)
      ·
        refine ⟨1870672344493310922443437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9976919170630991586364997 1870672344493310922443437)
        ·
          refine ⟨701502129184991595916289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1870672344493310922443437 701502129184991595916289)
          ·
            refine ⟨526126596888743696937217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701502129184991595916289 526126596888743696937217)
            ·
              refine ⟨394594947666557772702913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526126596888743696937217 394594947666557772702913)
              ·
                refine ⟨295946210749918329527185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394594947666557772702913 295946210749918329527185)
                ·
                  refine ⟨221959658062438747145389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295946210749918329527185 221959658062438747145389)
                  ·
                    rfl

theorem cell20_486298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_486298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486298 prefixEnd_486298 := by exact prefixLift 486298
  have htrace : WordTrace (prefixWord ++ tailWord_486298) baseStart_486298 baseEnd_486298 := by
    simpa [prefixWord, tailWord_486298, baseEnd_486298] using wordTrace_append hprefix tailTrace_486298
  have hstable : (prefixWord ++ tailWord_486298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486298).length < 2 ^ (prefixWord ++ tailWord_486298).sum := by decide
  have hdescent : baseEnd_486298 < baseStart_486298 := by decide
  rcases family_descends (prefixWord ++ tailWord_486298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486330 : List Nat := [3, 1, 1, 1, 2, 1, 7, 4]
def baseStart_486330 : Nat := 118140960795 + 486330 * 2 ^ 59
def prefixEnd_486330 : Nat := 4983230072969 + 3 ^ 40 * 486330 * 2
def baseEnd_486330 : Nat := 73991421244796286026197

theorem tailTrace_486330 : CollatzResearch.WordTrace tailWord_486330 prefixEnd_486330 73991421244796286026197 := by
  unfold tailWord_486330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4434478082029235849120111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11825274885411295597653629 4434478082029235849120111)
  ·
    refine ⟨6651717123043853773680167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4434478082029235849120111 6651717123043853773680167)
    ·
      refine ⟨9977575684565780660520251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6651717123043853773680167 9977575684565780660520251)
      ·
        refine ⟨14966363526848670990780377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9977575684565780660520251 14966363526848670990780377)
        ·
          refine ⟨11224772645136503243085283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14966363526848670990780377 11224772645136503243085283)
          ·
            refine ⟨16837158967704754864627925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11224772645136503243085283 16837158967704754864627925)
            ·
              refine ⟨394620913305580192139717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16837158967704754864627925 394620913305580192139717)
              ·
                refine ⟨73991421244796286026197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394620913305580192139717 73991421244796286026197)
                ·
                  rfl

theorem cell20_486330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_486330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486330 prefixEnd_486330 := by exact prefixLift 486330
  have htrace : WordTrace (prefixWord ++ tailWord_486330) baseStart_486330 baseEnd_486330 := by
    simpa [prefixWord, tailWord_486330, baseEnd_486330] using wordTrace_append hprefix tailTrace_486330
  have hstable : (prefixWord ++ tailWord_486330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486330).length < 2 ^ (prefixWord ++ tailWord_486330).sum := by decide
  have hdescent : baseEnd_486330 < baseStart_486330 := by decide
  rcases family_descends (prefixWord ++ tailWord_486330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486351 : List Nat := [1, 1, 2, 1, 1, 7, 7]
def baseStart_486351 : Nat := 118140960795 + 486351 * 2 ^ 59
def prefixEnd_486351 : Nat := 4983230072969 + 3 ^ 40 * 486351 * 2
def baseEnd_486351 : Nat := 24664872078511790930945

theorem tailTrace_486351 : CollatzResearch.WordTrace tailWord_486351 prefixEnd_486351 24664872078511790930945 := by
  unfold tailWord_486351
  simp only [CollatzResearch.WordTrace]
  refine ⟨17738678261040863982994907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11825785507360575988663271 17738678261040863982994907)
  ·
    refine ⟨26608017391561295974492361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17738678261040863982994907 26608017391561295974492361)
    ·
      refine ⟨19956013043670971980869271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26608017391561295974492361 19956013043670971980869271)
      ·
        refine ⟨29934019565506457971303907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19956013043670971980869271 29934019565506457971303907)
        ·
          refine ⟨44901029348259686956955861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29934019565506457971303907 44901029348259686956955861)
          ·
            refine ⟨1052367875349836413053653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 44901029348259686956955861 1052367875349836413053653)
            ·
              refine ⟨24664872078511790930945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1052367875349836413053653 24664872078511790930945)
              ·
                rfl

theorem cell20_486351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 7].length) (baseStart_486351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486351 prefixEnd_486351 := by exact prefixLift 486351
  have htrace : WordTrace (prefixWord ++ tailWord_486351) baseStart_486351 baseEnd_486351 := by
    simpa [prefixWord, tailWord_486351, baseEnd_486351] using wordTrace_append hprefix tailTrace_486351
  have hstable : (prefixWord ++ tailWord_486351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486351).length < 2 ^ (prefixWord ++ tailWord_486351).sum := by decide
  have hdescent : baseEnd_486351 < baseStart_486351 := by decide
  rcases family_descends (prefixWord ++ tailWord_486351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486354 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_486354 : Nat := 118140960795 + 486354 * 2 ^ 59
def prefixEnd_486354 : Nat := 4983230072969 + 3 ^ 40 * 486354 * 2
def baseEnd_486354 : Nat := 221985217988351441278493

theorem tailTrace_486354 : CollatzResearch.WordTrace tailWord_486354 prefixEnd_486354 221985217988351441278493 := by
  unfold tailWord_486354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4434696920007498873838529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11825858453353330330236077 4434696920007498873838529)
  ·
    refine ⟨3326022690005624155378897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4434696920007498873838529 3326022690005624155378897)
    ·
      refine ⟨2494517017504218116534173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3326022690005624155378897 2494517017504218116534173)
      ·
        refine ⟨935443881564081793700315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2494517017504218116534173 935443881564081793700315)
        ·
          refine ⟨1403165822346122690550473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935443881564081793700315 1403165822346122690550473)
          ·
            refine ⟨1052374366759592017912855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1403165822346122690550473 1052374366759592017912855)
            ·
              refine ⟨1578561550139388026869283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052374366759592017912855 1578561550139388026869283)
              ·
                refine ⟨2367842325209082040303925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578561550139388026869283 2367842325209082040303925)
                ·
                  refine ⟨221985217988351441278493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2367842325209082040303925 221985217988351441278493)
                  ·
                    rfl

theorem cell20_486354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_486354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486354 prefixEnd_486354 := by exact prefixLift 486354
  have htrace : WordTrace (prefixWord ++ tailWord_486354) baseStart_486354 baseEnd_486354 := by
    simpa [prefixWord, tailWord_486354, baseEnd_486354] using wordTrace_append hprefix tailTrace_486354
  have hstable : (prefixWord ++ tailWord_486354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486354).length < 2 ^ (prefixWord ++ tailWord_486354).sum := by decide
  have hdescent : baseEnd_486354 < baseStart_486354 := by decide
  rcases family_descends (prefixWord ++ tailWord_486354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486361 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 4]
def baseStart_486361 : Nat := 118140960795 + 486361 * 2 ^ 59
def prefixEnd_486361 : Nat := 4983230072969 + 3 ^ 40 * 486361 * 2
def baseEnd_486361 : Nat := 221988412979090528045131

theorem tailTrace_486361 : CollatzResearch.WordTrace tailWord_486361 prefixEnd_486361 221988412979090528045131 := by
  unfold tailWord_486361
  simp only [CollatzResearch.WordTrace]
  refine ⟨17739042991004635690858937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11826028660669757127239291 17739042991004635690858937)
  ·
    refine ⟨13304282243253476768144203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17739042991004635690858937 13304282243253476768144203)
    ·
      refine ⟨19956423364880215152216305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13304282243253476768144203 19956423364880215152216305)
      ·
        refine ⟨14967317523660161364162229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19956423364880215152216305 14967317523660161364162229)
        ·
          refine ⟨1403186017843140127890209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14967317523660161364162229 1403186017843140127890209)
          ·
            refine ⟨1052389513382355095917657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1403186017843140127890209 1052389513382355095917657)
            ·
              refine ⟨789292135036766321938243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1052389513382355095917657 789292135036766321938243)
              ·
                refine ⟨1183938202555149482907365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789292135036766321938243 1183938202555149482907365)
                ·
                  refine ⟨221988412979090528045131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1183938202555149482907365 221988412979090528045131)
                  ·
                    rfl

theorem cell20_486361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_486361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486361 prefixEnd_486361 := by exact prefixLift 486361
  have htrace : WordTrace (prefixWord ++ tailWord_486361) baseStart_486361 baseEnd_486361 := by
    simpa [prefixWord, tailWord_486361, baseEnd_486361] using wordTrace_append hprefix tailTrace_486361
  have hstable : (prefixWord ++ tailWord_486361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486361).length < 2 ^ (prefixWord ++ tailWord_486361).sum := by decide
  have hdescent : baseEnd_486361 < baseStart_486361 := by decide
  rcases family_descends (prefixWord ++ tailWord_486361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486385 : List Nat := [1, 2, 2, 2, 4, 3, 2, 4]
def baseStart_486385 : Nat := 118140960795 + 486385 * 2 ^ 59
def prefixEnd_486385 : Nat := 4983230072969 + 3 ^ 40 * 486385 * 2
def baseEnd_486385 : Nat := 73999789077684370415011

theorem tailTrace_486385 : CollatzResearch.WordTrace tailWord_486385 prefixEnd_486385 73999789077684370415011 := by
  unfold tailWord_486385
  simp only [CollatzResearch.WordTrace]
  refine ⟨17739918342917687789732609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11826612228611791859821739 17739918342917687789732609)
  ·
    refine ⟨13304938757188265842299457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17739918342917687789732609 13304938757188265842299457)
    ·
      refine ⟨9978704067891199381724593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13304938757188265842299457 9978704067891199381724593)
      ·
        refine ⟨7484028050918399536293445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9978704067891199381724593 7484028050918399536293445)
        ·
          refine ⟨1403255259547199913055021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7484028050918399536293445 1403255259547199913055021)
          ·
            refine ⟨526220722330199967395633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1403255259547199913055021 526220722330199967395633)
            ·
              refine ⟨394665541747649975546725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526220722330199967395633 394665541747649975546725)
              ·
                refine ⟨73999789077684370415011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394665541747649975546725 73999789077684370415011)
                ·
                  rfl

theorem cell20_486385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 4].length) (baseStart_486385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486385 prefixEnd_486385 := by exact prefixLift 486385
  have htrace : WordTrace (prefixWord ++ tailWord_486385) baseStart_486385 baseEnd_486385 := by
    simpa [prefixWord, tailWord_486385, baseEnd_486385] using wordTrace_append hprefix tailTrace_486385
  have hstable : (prefixWord ++ tailWord_486385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486385).length < 2 ^ (prefixWord ++ tailWord_486385).sum := by decide
  have hdescent : baseEnd_486385 < baseStart_486385 := by decide
  rcases family_descends (prefixWord ++ tailWord_486385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486402 : List Nat := [3, 4, 1, 3, 1, 2, 6]
def baseStart_486402 : Nat := 118140960795 + 486402 * 2 ^ 59
def prefixEnd_486402 : Nat := 4983230072969 + 3 ^ 40 * 486402 * 2
def baseEnd_486402 : Nat := 24667458499586289742033

theorem tailTrace_486402 : CollatzResearch.WordTrace tailWord_486402 prefixEnd_486402 24667458499586289742033 := by
  unfold tailWord_486402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4435134595964024923275365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11827025589237399795400973 4435134595964024923275365)
  ·
    refine ⟨831587736743254673114131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4435134595964024923275365 831587736743254673114131)
    ·
      refine ⟨1247381605114882009671197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 831587736743254673114131 1247381605114882009671197)
      ·
        refine ⟨467768101918080753626699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1247381605114882009671197 467768101918080753626699)
        ·
          refine ⟨701652152877121130440049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467768101918080753626699 701652152877121130440049)
          ·
            refine ⟨526239114657840847830037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701652152877121130440049 526239114657840847830037)
            ·
              refine ⟨24667458499586289742033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 526239114657840847830037 24667458499586289742033)
              ·
                rfl

theorem cell20_486402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 6].length) (baseStart_486402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486402 prefixEnd_486402 := by exact prefixLift 486402
  have htrace : WordTrace (prefixWord ++ tailWord_486402) baseStart_486402 baseEnd_486402 := by
    simpa [prefixWord, tailWord_486402, baseEnd_486402] using wordTrace_append hprefix tailTrace_486402
  have hstable : (prefixWord ++ tailWord_486402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486402).length < 2 ^ (prefixWord ++ tailWord_486402).sum := by decide
  have hdescent : baseEnd_486402 < baseStart_486402 := by decide
  rcases family_descends (prefixWord ++ tailWord_486402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486465 : List Nat := [1, 2, 5, 1, 11]
def baseStart_486465 : Nat := 118140960795 + 486465 * 2 ^ 59
def prefixEnd_486465 : Nat := 4983230072969 + 3 ^ 40 * 486465 * 2
def baseEnd_486465 : Nat := 2741183721147264056519

theorem tailTrace_486465 : CollatzResearch.WordTrace tailWord_486465 prefixEnd_486465 2741183721147264056519 := by
  unfold tailWord_486465
  simp only [CollatzResearch.WordTrace]
  refine ⟨17742836182627861452644849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11828557455085240968429899 17742836182627861452644849)
  ·
    refine ⟨13307127136970896089483637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17742836182627861452644849 13307127136970896089483637)
    ·
      refine ⟨1247543169091021508389091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13307127136970896089483637 1247543169091021508389091)
      ·
        refine ⟨1871314753636532262583637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1247543169091021508389091 1871314753636532262583637)
        ·
          refine ⟨2741183721147264056519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1871314753636532262583637 2741183721147264056519)
          ·
            rfl

theorem cell20_486465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 11].length) (baseStart_486465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486465 prefixEnd_486465 := by exact prefixLift 486465
  have htrace : WordTrace (prefixWord ++ tailWord_486465) baseStart_486465 baseEnd_486465 := by
    simpa [prefixWord, tailWord_486465, baseEnd_486465] using wordTrace_append hprefix tailTrace_486465
  have hstable : (prefixWord ++ tailWord_486465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486465).length < 2 ^ (prefixWord ++ tailWord_486465).sum := by decide
  have hdescent : baseEnd_486465 < baseStart_486465 := by decide
  rcases family_descends (prefixWord ++ tailWord_486465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486471 : List Nat := [1, 1, 4, 1, 3, 4, 2, 2, 2]
def baseStart_486471 : Nat := 118140960795 + 486471 * 2 ^ 59
def prefixEnd_486471 : Nat := 4983230072969 + 3 ^ 40 * 486471 * 2
def baseEnd_486471 : Nat := 222038619976419034378015

theorem tailTrace_486471 : CollatzResearch.WordTrace tailWord_486471 prefixEnd_486471 222038619976419034378015 := by
  unfold tailWord_486471
  simp only [CollatzResearch.WordTrace]
  refine ⟨17743055020606124477363267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11828703347070749651575511 17743055020606124477363267)
  ·
    refine ⟨26614582530909186716044901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17743055020606124477363267 26614582530909186716044901)
    ·
      refine ⟨4990234224545472509258419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26614582530909186716044901 4990234224545472509258419)
      ·
        refine ⟨7485351336818208763887629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4990234224545472509258419 7485351336818208763887629)
        ·
          refine ⟨2807006751306828286457861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7485351336818208763887629 2807006751306828286457861)
          ·
            refine ⟨526313765870030303710849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2807006751306828286457861 526313765870030303710849)
            ·
              refine ⟨394735324402522727783137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526313765870030303710849 394735324402522727783137)
              ·
                refine ⟨296051493301892045837353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394735324402522727783137 296051493301892045837353)
                ·
                  refine ⟨222038619976419034378015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296051493301892045837353 222038619976419034378015)
                  ·
                    rfl

theorem cell20_486471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 2].length) (baseStart_486471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486471 prefixEnd_486471 := by exact prefixLift 486471
  have htrace : WordTrace (prefixWord ++ tailWord_486471) baseStart_486471 baseEnd_486471 := by
    simpa [prefixWord, tailWord_486471, baseEnd_486471] using wordTrace_append hprefix tailTrace_486471
  have hstable : (prefixWord ++ tailWord_486471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486471).length < 2 ^ (prefixWord ++ tailWord_486471).sum := by decide
  have hdescent : baseEnd_486471 < baseStart_486471 := by decide
  rcases family_descends (prefixWord ++ tailWord_486471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486482 : List Nat := [3, 2, 2, 1, 3, 1, 3, 5]
def baseStart_486482 : Nat := 118140960795 + 486482 * 2 ^ 59
def prefixEnd_486482 : Nat := 4983230072969 + 3 ^ 40 * 486482 * 2
def baseEnd_486482 : Nat := 74014546892050628337101

theorem tailTrace_486482 : CollatzResearch.WordTrace tailWord_486482 prefixEnd_486482 74014546892050628337101 := by
  unfold tailWord_486482
  simp only [CollatzResearch.WordTrace]
  refine ⟨4435864055891568339003425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11828970815710848904009133 4435864055891568339003425)
  ·
    refine ⟨3326898041918676254252569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4435864055891568339003425 3326898041918676254252569)
    ·
      refine ⟨2495173531439007190689427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3326898041918676254252569 2495173531439007190689427)
      ·
        refine ⟨3742760297158510786034141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2495173531439007190689427 3742760297158510786034141)
        ·
          refine ⟨1403535111434441544762803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3742760297158510786034141 1403535111434441544762803)
          ·
            refine ⟨2105302667151662317144205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403535111434441544762803 2105302667151662317144205)
            ·
              refine ⟨789488500181873368929077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2105302667151662317144205 789488500181873368929077)
              ·
                refine ⟨74014546892050628337101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 789488500181873368929077 74014546892050628337101)
                ·
                  rfl

theorem cell20_486482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_486482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486482 prefixEnd_486482 := by exact prefixLift 486482
  have htrace : WordTrace (prefixWord ++ tailWord_486482) baseStart_486482 baseEnd_486482 := by
    simpa [prefixWord, tailWord_486482, baseEnd_486482] using wordTrace_append hprefix tailTrace_486482
  have hstable : (prefixWord ++ tailWord_486482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486482).length < 2 ^ (prefixWord ++ tailWord_486482).sum := by decide
  have hdescent : baseEnd_486482 < baseStart_486482 := by decide
  rcases family_descends (prefixWord ++ tailWord_486482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486496 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 4]
def baseStart_486496 : Nat := 118140960795 + 486496 * 2 ^ 59
def prefixEnd_486496 : Nat := 4983230072969 + 3 ^ 40 * 486496 * 2
def baseEnd_486496 : Nat := 222050030657630058544579

theorem tailTrace_486496 : CollatzResearch.WordTrace tailWord_486496 prefixEnd_486496 222050030657630058544579 := by
  unfold tailWord_486496
  simp only [CollatzResearch.WordTrace]
  refine ⟨8871983422757776873511671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11829311230343702498015561 8871983422757776873511671)
  ·
    refine ⟨13307975134136665310267507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8871983422757776873511671 13307975134136665310267507)
    ·
      refine ⟨19961962701204997965401261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13307975134136665310267507 19961962701204997965401261)
      ·
        refine ⟨7485736012951874237025473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19961962701204997965401261 7485736012951874237025473)
        ·
          refine ⟨5614302009713905677769105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7485736012951874237025473 5614302009713905677769105)
          ·
            refine ⟨4210726507285429258326829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5614302009713905677769105 4210726507285429258326829)
            ·
              refine ⟨1579022440232035971872561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4210726507285429258326829 1579022440232035971872561)
              ·
                refine ⟨1184266830174026978904421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1579022440232035971872561 1184266830174026978904421)
                ·
                  refine ⟨222050030657630058544579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1184266830174026978904421 222050030657630058544579)
                  ·
                    rfl

theorem cell20_486496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_486496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486496 prefixEnd_486496 := by exact prefixLift 486496
  have htrace : WordTrace (prefixWord ++ tailWord_486496) baseStart_486496 baseEnd_486496 := by
    simpa [prefixWord, tailWord_486496, baseEnd_486496] using wordTrace_append hprefix tailTrace_486496
  have hstable : (prefixWord ++ tailWord_486496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486496).length < 2 ^ (prefixWord ++ tailWord_486496).sum := by decide
  have hdescent : baseEnd_486496 < baseStart_486496 := by decide
  rcases family_descends (prefixWord ++ tailWord_486496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486526 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 4]
def baseStart_486526 : Nat := 118140960795 + 486526 * 2 ^ 59
def prefixEnd_486526 : Nat := 4983230072969 + 3 ^ 40 * 486526 * 2
def baseEnd_486526 : Nat := 222063723475083287544457

theorem tailTrace_486526 : CollatzResearch.WordTrace tailWord_486526 prefixEnd_486526 222063723475083287544457 := by
  unfold tailWord_486526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2218132629425858608826929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11830040690271245913743621 2218132629425858608826929)
  ·
    refine ⟨1663599472069393956620197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2218132629425858608826929 1663599472069393956620197)
    ·
      refine ⟨311924901013011366866287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1663599472069393956620197 311924901013011366866287)
      ·
        refine ⟨467887351519517050299431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311924901013011366866287 467887351519517050299431)
        ·
          refine ⟨701831027279275575449147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467887351519517050299431 701831027279275575449147)
          ·
            refine ⟨1052746540918913363173721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701831027279275575449147 1052746540918913363173721)
            ·
              refine ⟨789559905689185022380291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1052746540918913363173721 789559905689185022380291)
              ·
                refine ⟨1184339858533777533570437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789559905689185022380291 1184339858533777533570437)
                ·
                  refine ⟨222063723475083287544457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1184339858533777533570437 222063723475083287544457)
                  ·
                    rfl

theorem cell20_486526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_486526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486526 prefixEnd_486526 := by exact prefixLift 486526
  have htrace : WordTrace (prefixWord ++ tailWord_486526) baseStart_486526 baseEnd_486526 := by
    simpa [prefixWord, tailWord_486526, baseEnd_486526] using wordTrace_append hprefix tailTrace_486526
  have hstable : (prefixWord ++ tailWord_486526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486526).length < 2 ^ (prefixWord ++ tailWord_486526).sum := by decide
  have hdescent : baseEnd_486526 < baseStart_486526 := by decide
  rcases family_descends (prefixWord ++ tailWord_486526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486589 : List Nat := [1, 4, 1, 2, 1, 1, 2, 6, 2]
def baseStart_486589 : Nat := 118140960795 + 486589 * 2 ^ 59
def prefixEnd_486589 : Nat := 4983230072969 + 3 ^ 40 * 486589 * 2
def baseEnd_486589 : Nat := 222092478391735068444199

theorem tailTrace_486589 : CollatzResearch.WordTrace tailWord_486589 prefixEnd_486589 222092478391735068444199 := by
  unfold tailWord_486589
  simp only [CollatzResearch.WordTrace]
  refine ⟨17747358834178630630158821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11831572556119087086772547 17747358834178630630158821)
  ·
    refine ⟨3327629781408493243154779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17747358834178630630158821 3327629781408493243154779)
    ·
      refine ⟨4991444672112739864732169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3327629781408493243154779 4991444672112739864732169)
      ·
        refine ⟨3743583504084554898549127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4991444672112739864732169 3743583504084554898549127)
        ·
          refine ⟨5615375256126832347823691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3743583504084554898549127 5615375256126832347823691)
          ·
            refine ⟨8423062884190248521735537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5615375256126832347823691 8423062884190248521735537)
            ·
              refine ⟨6317297163142686391301653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8423062884190248521735537 6317297163142686391301653)
              ·
                refine ⟨296123304522313424592265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6317297163142686391301653 296123304522313424592265)
                ·
                  refine ⟨222092478391735068444199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296123304522313424592265 222092478391735068444199)
                  ·
                    rfl

theorem cell20_486589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_486589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486589 prefixEnd_486589 := by exact prefixLift 486589
  have htrace : WordTrace (prefixWord ++ tailWord_486589) baseStart_486589 baseEnd_486589 := by
    simpa [prefixWord, tailWord_486589, baseEnd_486589] using wordTrace_append hprefix tailTrace_486589
  have hstable : (prefixWord ++ tailWord_486589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486589).length < 2 ^ (prefixWord ++ tailWord_486589).sum := by decide
  have hdescent : baseEnd_486589 < baseStart_486589 := by decide
  rcases family_descends (prefixWord ++ tailWord_486589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486610 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_486610 : Nat := 118140960795 + 486610 * 2 ^ 59
def prefixEnd_486610 : Nat := 4983230072969 + 3 ^ 40 * 486610 * 2
def baseEnd_486610 : Nat := 222102063363952328744113

theorem tailTrace_486610 : CollatzResearch.WordTrace tailWord_486610 prefixEnd_486610 222102063363952328744113 := by
  unfold tailWord_486610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4437031191775637804168321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11832083178068367477782189 4437031191775637804168321)
  ·
    refine ⟨3327773393831728353126241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4437031191775637804168321 3327773393831728353126241)
    ·
      refine ⟨2495830045373796264844681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3327773393831728353126241 2495830045373796264844681)
      ·
        refine ⟨1871872534030347198633511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2495830045373796264844681 1871872534030347198633511)
        ·
          refine ⟨2807808801045520797950267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1871872534030347198633511 2807808801045520797950267)
          ·
            refine ⟨4211713201568281196925401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807808801045520797950267 4211713201568281196925401)
            ·
              refine ⟨3158784901176210897694051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4211713201568281196925401 3158784901176210897694051)
              ·
                refine ⟨4738177351764316346541077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3158784901176210897694051 4738177351764316346541077)
                ·
                  refine ⟨222102063363952328744113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4738177351764316346541077 222102063363952328744113)
                  ·
                    rfl

theorem cell20_486610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_486610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486610 prefixEnd_486610 := by exact prefixLift 486610
  have htrace : WordTrace (prefixWord ++ tailWord_486610) baseStart_486610 baseEnd_486610 := by
    simpa [prefixWord, tailWord_486610, baseEnd_486610] using wordTrace_append hprefix tailTrace_486610
  have hstable : (prefixWord ++ tailWord_486610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486610).length < 2 ^ (prefixWord ++ tailWord_486610).sum := by decide
  have hdescent : baseEnd_486610 < baseStart_486610 := by decide
  rcases family_descends (prefixWord ++ tailWord_486610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486655 : List Nat := [1, 1, 2, 2, 1, 5, 3, 5]
def baseStart_486655 : Nat := 118140960795 + 486655 * 2 ^ 59
def prefixEnd_486655 : Nat := 4983230072969 + 3 ^ 40 * 486655 * 2
def baseEnd_486655 : Nat := 74040867530044057414643

theorem tailTrace_486655 : CollatzResearch.WordTrace tailWord_486655 prefixEnd_486655 74040867530044057414643 := by
  unfold tailWord_486655
  simp only [CollatzResearch.WordTrace]
  refine ⟨17749766051939523902061419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11833177367959682601374279 17749766051939523902061419)
  ·
    refine ⟨26624649077909285853092129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17749766051939523902061419 26624649077909285853092129)
    ·
      refine ⟨19968486808431964389819097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26624649077909285853092129 19968486808431964389819097)
      ·
        refine ⟨14976365106323973292364323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19968486808431964389819097 14976365106323973292364323)
        ·
          refine ⟨22464547659485959938546485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14976365106323973292364323 22464547659485959938546485)
          ·
            refine ⟨2106051343076808744238733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22464547659485959938546485 2106051343076808744238733)
            ·
              refine ⟨789769253653803279089525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2106051343076808744238733 789769253653803279089525)
              ·
                refine ⟨74040867530044057414643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 789769253653803279089525 74040867530044057414643)
                ·
                  rfl

theorem cell20_486655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 5].length) (baseStart_486655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486655 prefixEnd_486655 := by exact prefixLift 486655
  have htrace : WordTrace (prefixWord ++ tailWord_486655) baseStart_486655 baseEnd_486655 := by
    simpa [prefixWord, tailWord_486655, baseEnd_486655] using wordTrace_append hprefix tailTrace_486655
  have hstable : (prefixWord ++ tailWord_486655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486655).length < 2 ^ (prefixWord ++ tailWord_486655).sum := by decide
  have hdescent : baseEnd_486655 < baseStart_486655 := by decide
  rcases family_descends (prefixWord ++ tailWord_486655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486682 : List Nat := [3, 1, 1, 3, 3, 2, 2, 3, 2]
def baseStart_486682 : Nat := 118140960795 + 486682 * 2 ^ 59
def prefixEnd_486682 : Nat := 4983230072969 + 3 ^ 40 * 486682 * 2
def baseEnd_486682 : Nat := 222134926125840078343819

theorem tailTrace_486682 : CollatzResearch.WordTrace tailWord_486682 prefixEnd_486682 222134926125840078343819 := by
  unfold tailWord_486682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4437687705710426878323575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11833833881894471675529533 4437687705710426878323575)
  ·
    refine ⟨6656531558565640317485363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4437687705710426878323575 6656531558565640317485363)
    ·
      refine ⟨9984797337848460476228045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6656531558565640317485363 9984797337848460476228045)
      ·
        refine ⟨3744299001693172678585517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9984797337848460476228045 3744299001693172678585517)
        ·
          refine ⟨1404112125634939754469569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3744299001693172678585517 1404112125634939754469569)
          ·
            refine ⟨1053084094226204815852177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1404112125634939754469569 1053084094226204815852177)
            ·
              refine ⟨789813070669653611889133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053084094226204815852177 789813070669653611889133)
              ·
                refine ⟨296179901501120104458425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 789813070669653611889133 296179901501120104458425)
                ·
                  refine ⟨222134926125840078343819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296179901501120104458425 222134926125840078343819)
                  ·
                    rfl

theorem cell20_486682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_486682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486682 prefixEnd_486682 := by exact prefixLift 486682
  have htrace : WordTrace (prefixWord ++ tailWord_486682) baseStart_486682 baseEnd_486682 := by
    simpa [prefixWord, tailWord_486682, baseEnd_486682] using wordTrace_append hprefix tailTrace_486682
  have hstable : (prefixWord ++ tailWord_486682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486682).length < 2 ^ (prefixWord ++ tailWord_486682).sum := by decide
  have hdescent : baseEnd_486682 < baseStart_486682 := by decide
  rcases family_descends (prefixWord ++ tailWord_486682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486693 : List Nat := [1, 3, 1, 2, 4, 2, 7]
def baseStart_486693 : Nat := 118140960795 + 486693 * 2 ^ 59
def prefixEnd_486693 : Nat := 4983230072969 + 3 ^ 40 * 486693 * 2
def baseEnd_486693 : Nat := 24682216313952547664123

theorem tailTrace_486693 : CollatzResearch.WordTrace tailWord_486693 prefixEnd_486693 24682216313952547664123 := by
  unfold tailWord_486693
  simp only [CollatzResearch.WordTrace]
  refine ⟨17751152025801856391944733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11834101350534570927963155 17751152025801856391944733)
  ·
    refine ⟨6656682009675696146979275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17751152025801856391944733 6656682009675696146979275)
    ·
      refine ⟨9985023014513544220468913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6656682009675696146979275 9985023014513544220468913)
      ·
        refine ⟨7488767260885158165351685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9985023014513544220468913 7488767260885158165351685)
        ·
          refine ⟨1404143861415967156003441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7488767260885158165351685 1404143861415967156003441)
          ·
            refine ⟨1053107896061975367002581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1404143861415967156003441 1053107896061975367002581)
            ·
              refine ⟨24682216313952547664123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1053107896061975367002581 24682216313952547664123)
              ·
                rfl

theorem cell20_486693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 7].length) (baseStart_486693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486693 prefixEnd_486693 := by exact prefixLift 486693
  have htrace : WordTrace (prefixWord ++ tailWord_486693) baseStart_486693 baseEnd_486693 := by
    simpa [prefixWord, tailWord_486693, baseEnd_486693] using wordTrace_append hprefix tailTrace_486693
  have hstable : (prefixWord ++ tailWord_486693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486693).length < 2 ^ (prefixWord ++ tailWord_486693).sum := by decide
  have hdescent : baseEnd_486693 < baseStart_486693 := by decide
  rcases family_descends (prefixWord ++ tailWord_486693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486696 : List Nat := [2, 1, 5, 1, 2, 1, 3, 2, 3]
def baseStart_486696 : Nat := 118140960795 + 486696 * 2 ^ 59
def prefixEnd_486696 : Nat := 4983230072969 + 3 ^ 40 * 486696 * 2
def baseEnd_486696 : Nat := 222141316107318251877095

theorem tailTrace_486696 : CollatzResearch.WordTrace tailWord_486696 prefixEnd_486696 222141316107318251877095 := by
  unfold tailWord_486696
  simp only [CollatzResearch.WordTrace]
  refine ⟨8875630722395493952151971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11834174296527325269535961 8875630722395493952151971)
  ·
    refine ⟨13313446083593240928227957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8875630722395493952151971 13313446083593240928227957)
    ·
      refine ⟨1248135570336866337021371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13313446083593240928227957 1248135570336866337021371)
      ·
        refine ⟨1872203355505299505532057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1248135570336866337021371 1872203355505299505532057)
        ·
          refine ⟨1404152516628974629149043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1872203355505299505532057 1404152516628974629149043)
          ·
            refine ⟨2106228774943461943723565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1404152516628974629149043 2106228774943461943723565)
            ·
              refine ⟨789835790603798228896337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2106228774943461943723565 789835790603798228896337)
              ·
                refine ⟨592376842952848671672253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 789835790603798228896337 592376842952848671672253)
                ·
                  refine ⟨222141316107318251877095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 592376842952848671672253 222141316107318251877095)
                  ·
                    rfl

theorem cell20_486696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_486696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486696 prefixEnd_486696 := by exact prefixLift 486696
  have htrace : WordTrace (prefixWord ++ tailWord_486696) baseStart_486696 baseEnd_486696 := by
    simpa [prefixWord, tailWord_486696, baseEnd_486696] using wordTrace_append hprefix tailTrace_486696
  have hstable : (prefixWord ++ tailWord_486696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486696).length < 2 ^ (prefixWord ++ tailWord_486696).sum := by decide
  have hdescent : baseEnd_486696 < baseStart_486696 := by decide
  rcases family_descends (prefixWord ++ tailWord_486696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486713 : List Nat := [1, 2, 1, 6, 2, 1, 3, 1, 3]
def baseStart_486713 : Nat := 118140960795 + 486713 * 2 ^ 59
def prefixEnd_486713 : Nat := 4983230072969 + 3 ^ 40 * 486713 * 2
def baseEnd_486713 : Nat := 222149075370541748310359

theorem tailTrace_486713 : CollatzResearch.WordTrace tailWord_486713 prefixEnd_486713 222149075370541748310359 := by
  unfold tailWord_486713
  simp only [CollatzResearch.WordTrace]
  refine ⟨17751881485729399807672793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11834587657152933205115195 17751881485729399807672793)
  ·
    refine ⟨13313911114297049855754595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17751881485729399807672793 13313911114297049855754595)
    ·
      refine ⟨19970866671445574783631893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13313911114297049855754595 19970866671445574783631893)
      ·
        refine ⟨936134375224011317982745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19970866671445574783631893 936134375224011317982745)
        ·
          refine ⟨702100781418008488487059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 936134375224011317982745 702100781418008488487059)
          ·
            refine ⟨1053151172127012732730589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702100781418008488487059 1053151172127012732730589)
            ·
              refine ⟨394931689547629774773971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1053151172127012732730589 394931689547629774773971)
              ·
                refine ⟨592397534321444662160957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394931689547629774773971 592397534321444662160957)
                ·
                  refine ⟨222149075370541748310359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 592397534321444662160957 222149075370541748310359)
                  ·
                    rfl

theorem cell20_486713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 3].length) (baseStart_486713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486713 prefixEnd_486713 := by exact prefixLift 486713
  have htrace : WordTrace (prefixWord ++ tailWord_486713) baseStart_486713 baseEnd_486713 := by
    simpa [prefixWord, tailWord_486713, baseEnd_486713] using wordTrace_append hprefix tailTrace_486713
  have hstable : (prefixWord ++ tailWord_486713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486713).length < 2 ^ (prefixWord ++ tailWord_486713).sum := by decide
  have hdescent : baseEnd_486713 < baseStart_486713 := by decide
  rcases family_descends (prefixWord ++ tailWord_486713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486733 : List Nat := [1, 6, 1, 3, 2, 1, 1, 3, 2]
def baseStart_486733 : Nat := 118140960795 + 486733 * 2 ^ 59
def prefixEnd_486733 : Nat := 4983230072969 + 3 ^ 40 * 486733 * 2
def baseEnd_486733 : Nat := 222158203915510567643611

theorem tailTrace_486733 : CollatzResearch.WordTrace tailWord_486733 prefixEnd_486733 222158203915510567643611 := by
  unfold tailWord_486733
  simp only [CollatzResearch.WordTrace]
  refine ⟨17752610945656943223400853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11835073963771295482267235 17752610945656943223400853)
  ·
    refine ⟨832153638077669213596915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17752610945656943223400853 832153638077669213596915)
    ·
      refine ⟨1248230457116503820395373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 832153638077669213596915 1248230457116503820395373)
      ·
        refine ⟨468086421418688932648265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1248230457116503820395373 468086421418688932648265)
        ·
          refine ⟨351064816064016699486199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468086421418688932648265 351064816064016699486199)
          ·
            refine ⟨526597224096025049229299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351064816064016699486199 526597224096025049229299)
            ·
              refine ⟨789895836144037573843949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526597224096025049229299 789895836144037573843949)
              ·
                refine ⟨296210938554014090191481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 789895836144037573843949 296210938554014090191481)
                ·
                  refine ⟨222158203915510567643611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296210938554014090191481 222158203915510567643611)
                  ·
                    rfl

theorem cell20_486733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_486733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486733 prefixEnd_486733 := by exact prefixLift 486733
  have htrace : WordTrace (prefixWord ++ tailWord_486733) baseStart_486733 baseEnd_486733 := by
    simpa [prefixWord, tailWord_486733, baseEnd_486733] using wordTrace_append hprefix tailTrace_486733
  have hstable : (prefixWord ++ tailWord_486733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486733).length < 2 ^ (prefixWord ++ tailWord_486733).sum := by decide
  have hdescent : baseEnd_486733 < baseStart_486733 := by decide
  rcases family_descends (prefixWord ++ tailWord_486733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486745 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 6]
def baseStart_486745 : Nat := 118140960795 + 486745 * 2 ^ 59
def prefixEnd_486745 : Nat := 4983230072969 + 3 ^ 40 * 486745 * 2
def baseEnd_486745 : Nat := 222163681042491859243561

theorem tailTrace_486745 : CollatzResearch.WordTrace tailWord_486745 prefixEnd_486745 222163681042491859243561 := by
  unfold tailWord_486745
  simp only [CollatzResearch.WordTrace]
  refine ⟨17753048621613469272837689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11835365747742312848558459 17753048621613469272837689)
  ·
    refine ⟨13314786466210101954628267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17753048621613469272837689 13314786466210101954628267)
    ·
      refine ⟨19972179699315152931942401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13314786466210101954628267 19972179699315152931942401)
      ·
        refine ⟨14979134774486364698956801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19972179699315152931942401 14979134774486364698956801)
        ·
          refine ⟨11234351080864773524217601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14979134774486364698956801 11234351080864773524217601)
          ·
            refine ⟨8425763310648580143163201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11234351080864773524217601 8425763310648580143163201)
            ·
              refine ⟨6319322482986435107372401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8425763310648580143163201 6319322482986435107372401)
              ·
                refine ⟨4739491862239826330529301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6319322482986435107372401 4739491862239826330529301)
                ·
                  refine ⟨222163681042491859243561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4739491862239826330529301 222163681042491859243561)
                  ·
                    rfl

theorem cell20_486745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_486745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486745 prefixEnd_486745 := by exact prefixLift 486745
  have htrace : WordTrace (prefixWord ++ tailWord_486745) baseStart_486745 baseEnd_486745 := by
    simpa [prefixWord, tailWord_486745, baseEnd_486745] using wordTrace_append hprefix tailTrace_486745
  have hstable : (prefixWord ++ tailWord_486745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486745).length < 2 ^ (prefixWord ++ tailWord_486745).sum := by decide
  have hdescent : baseEnd_486745 < baseStart_486745 := by decide
  rcases family_descends (prefixWord ++ tailWord_486745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486813 : List Nat := [1, 4, 2, 1, 3, 3, 2, 2, 2]
def baseStart_486813 : Nat := 118140960795 + 486813 * 2 ^ 59
def prefixEnd_486813 : Nat := 4983230072969 + 3 ^ 40 * 486813 * 2
def baseEnd_486813 : Nat := 222194718095385844976617

theorem tailTrace_486813 : CollatzResearch.WordTrace tailWord_486813 prefixEnd_486813 222194718095385844976617 := by
  unfold tailWord_486813
  simp only [CollatzResearch.WordTrace]
  refine ⟨17755528785367116886313093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11837019190244744590875395 17755528785367116886313093)
  ·
    refine ⟨3329161647256334416183705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17755528785367116886313093 3329161647256334416183705)
    ·
      refine ⟨2496871235442250812137779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3329161647256334416183705 2496871235442250812137779)
      ·
        refine ⟨3745306853163376218206669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2496871235442250812137779 3745306853163376218206669)
        ·
          refine ⟨1404490069936266081827501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3745306853163376218206669 1404490069936266081827501)
          ·
            refine ⟨526683776226099780685313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1404490069936266081827501 526683776226099780685313)
            ·
              refine ⟨395012832169574835513985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526683776226099780685313 395012832169574835513985)
              ·
                refine ⟨296259624127181126635489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395012832169574835513985 296259624127181126635489)
                ·
                  refine ⟨222194718095385844976617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296259624127181126635489 222194718095385844976617)
                  ·
                    rfl

theorem cell20_486813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_486813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486813 prefixEnd_486813 := by exact prefixLift 486813
  have htrace : WordTrace (prefixWord ++ tailWord_486813) baseStart_486813 baseEnd_486813 := by
    simpa [prefixWord, tailWord_486813, baseEnd_486813] using wordTrace_append hprefix tailTrace_486813
  have hstable : (prefixWord ++ tailWord_486813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486813).length < 2 ^ (prefixWord ++ tailWord_486813).sum := by decide
  have hdescent : baseEnd_486813 < baseStart_486813 := by decide
  rcases family_descends (prefixWord ++ tailWord_486813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486855 : List Nat := [1, 1, 4, 1, 1, 3, 4, 3, 2]
def baseStart_486855 : Nat := 118140960795 + 486855 * 2 ^ 59
def prefixEnd_486855 : Nat := 4983230072969 + 3 ^ 40 * 486855 * 2
def baseEnd_486855 : Nat := 222213888039820365576445

theorem tailTrace_486855 : CollatzResearch.WordTrace tailWord_486855 prefixEnd_486855 222213888039820365576445 := by
  unfold tailWord_486855
  simp only [CollatzResearch.WordTrace]
  refine ⟨17757060651214958059342019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11838040434143305372894679 17757060651214958059342019)
  ·
    refine ⟨26635590976822437089013029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17757060651214958059342019 26635590976822437089013029)
    ·
      refine ⟨4994173308154206954189943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26635590976822437089013029 4994173308154206954189943)
      ·
        refine ⟨7491259962231310431284915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4994173308154206954189943 7491259962231310431284915)
        ·
          refine ⟨11236889943346965646927373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7491259962231310431284915 11236889943346965646927373)
          ·
            refine ⟨4213833728755112117597765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11236889943346965646927373 4213833728755112117597765)
            ·
              refine ⟨790093824141583522049581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4213833728755112117597765 790093824141583522049581)
              ·
                refine ⟨296285184053093820768593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 790093824141583522049581 296285184053093820768593)
                ·
                  refine ⟨222213888039820365576445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296285184053093820768593 222213888039820365576445)
                  ·
                    rfl

theorem cell20_486855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 2].length) (baseStart_486855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486855 prefixEnd_486855 := by exact prefixLift 486855
  have htrace : WordTrace (prefixWord ++ tailWord_486855) baseStart_486855 baseEnd_486855 := by
    simpa [prefixWord, tailWord_486855, baseEnd_486855] using wordTrace_append hprefix tailTrace_486855
  have hstable : (prefixWord ++ tailWord_486855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486855).length < 2 ^ (prefixWord ++ tailWord_486855).sum := by decide
  have hdescent : baseEnd_486855 < baseStart_486855 := by decide
  rcases family_descends (prefixWord ++ tailWord_486855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486945 : List Nat := [1, 2, 3, 2, 2, 3, 1, 3, 3]
def baseStart_486945 : Nat := 118140960795 + 486945 * 2 ^ 59
def prefixEnd_486945 : Nat := 4983230072969 + 3 ^ 40 * 486945 * 2
def baseEnd_486945 : Nat := 222254966492180052576077

theorem tailTrace_486945 : CollatzResearch.WordTrace tailWord_486945 prefixEnd_486945 222254966492180052576077 := by
  unfold tailWord_486945
  simp only [CollatzResearch.WordTrace]
  refine ⟨17760343220888903430118289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11840228813925935620078859 17760343220888903430118289)
  ·
    refine ⟨13320257415666677572588717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17760343220888903430118289 13320257415666677572588717)
    ·
      refine ⟨4995096530875004089720769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13320257415666677572588717 4995096530875004089720769)
      ·
        refine ⟨3746322398156253067290577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4995096530875004089720769 3746322398156253067290577)
        ·
          refine ⟨2809741798617189800467933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3746322398156253067290577 2809741798617189800467933)
          ·
            refine ⟨1053653174481446175175475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2809741798617189800467933 1053653174481446175175475)
            ·
              refine ⟨1580479761722169262763213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053653174481446175175475 1580479761722169262763213)
              ·
                refine ⟨592679910645813473536205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1580479761722169262763213 592679910645813473536205)
                ·
                  refine ⟨222254966492180052576077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 592679910645813473536205 222254966492180052576077)
                  ·
                    rfl

theorem cell20_486945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_486945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_486945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_486945 prefixEnd_486945 := by exact prefixLift 486945
  have htrace : WordTrace (prefixWord ++ tailWord_486945) baseStart_486945 baseEnd_486945 := by
    simpa [prefixWord, tailWord_486945, baseEnd_486945] using wordTrace_append hprefix tailTrace_486945
  have hstable : (prefixWord ++ tailWord_486945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486945).length < 2 ^ (prefixWord ++ tailWord_486945).sum := by decide
  have hdescent : baseEnd_486945 < baseStart_486945 := by decide
  rcases family_descends (prefixWord ++ tailWord_486945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487011 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 6]
def baseStart_487011 : Nat := 118140960795 + 487011 * 2 ^ 59
def prefixEnd_487011 : Nat := 4983230072969 + 3 ^ 40 * 487011 * 2
def baseEnd_487011 : Nat := 222285090690577156375807

theorem tailTrace_487011 : CollatzResearch.WordTrace tailWord_487011 prefixEnd_487011 222285090690577156375807 := by
  unfold tailWord_487011
  simp only [CollatzResearch.WordTrace]
  refine ⟨17762750438649796702020887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11841833625766531134680591 17762750438649796702020887)
  ·
    refine ⟨26644125657974695053031331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17762750438649796702020887 26644125657974695053031331)
    ·
      refine ⟨39966188486962042579546997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26644125657974695053031331 39966188486962042579546997)
      ·
        refine ⟨3746830170652691491832531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39966188486962042579546997 3746830170652691491832531)
        ·
          refine ⟨5620245255979037237748797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3746830170652691491832531 5620245255979037237748797)
          ·
            refine ⟨2107591970992138964155799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5620245255979037237748797 2107591970992138964155799)
            ·
              refine ⟨3161387956488208446233699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2107591970992138964155799 3161387956488208446233699)
              ·
                refine ⟨4742081934732312669350549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3161387956488208446233699 4742081934732312669350549)
                ·
                  refine ⟨222285090690577156375807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4742081934732312669350549 222285090690577156375807)
                  ·
                    rfl

theorem cell20_487011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_487011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487011 prefixEnd_487011 := by exact prefixLift 487011
  have htrace : WordTrace (prefixWord ++ tailWord_487011) baseStart_487011 baseEnd_487011 := by
    simpa [prefixWord, tailWord_487011, baseEnd_487011] using wordTrace_append hprefix tailTrace_487011
  have hstable : (prefixWord ++ tailWord_487011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487011).length < 2 ^ (prefixWord ++ tailWord_487011).sum := by decide
  have hdescent : baseEnd_487011 < baseStart_487011 := by decide
  rcases family_descends (prefixWord ++ tailWord_487011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487049 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 4]
def baseStart_487049 : Nat := 118140960795 + 487049 * 2 ^ 59
def prefixEnd_487049 : Nat := 4983230072969 + 3 ^ 40 * 487049 * 2
def baseEnd_487049 : Nat := 222302434926017913108985

theorem tailTrace_487049 : CollatzResearch.WordTrace tailWord_487049 prefixEnd_487049 222302434926017913108985 := by
  unfold tailWord_487049
  simp only [CollatzResearch.WordTrace]
  refine ⟨17764136412512129191904201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11842757608341419461269467 17764136412512129191904201)
  ·
    refine ⟨13323102309384096893928151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17764136412512129191904201 13323102309384096893928151)
    ·
      refine ⟨19984653464076145340892227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13323102309384096893928151 19984653464076145340892227)
      ·
        refine ⟨29976980196114218011338341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19984653464076145340892227 29976980196114218011338341)
        ·
          refine ⟨5620683786771415877125939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29976980196114218011338341 5620683786771415877125939)
          ·
            refine ⟨8431025680157123815688909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5620683786771415877125939 8431025680157123815688909)
            ·
              refine ⟨3161634630058921430883341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8431025680157123815688909 3161634630058921430883341)
              ·
                refine ⟨1185612986272095536581253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3161634630058921430883341 1185612986272095536581253)
                ·
                  refine ⟨222302434926017913108985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1185612986272095536581253 222302434926017913108985)
                  ·
                    rfl

theorem cell20_487049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_487049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487049 prefixEnd_487049 := by exact prefixLift 487049
  have htrace : WordTrace (prefixWord ++ tailWord_487049) baseStart_487049 baseEnd_487049 := by
    simpa [prefixWord, tailWord_487049, baseEnd_487049] using wordTrace_append hprefix tailTrace_487049
  have hstable : (prefixWord ++ tailWord_487049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487049).length < 2 ^ (prefixWord ++ tailWord_487049).sum := by decide
  have hdescent : baseEnd_487049 < baseStart_487049 := by decide
  rcases family_descends (prefixWord ++ tailWord_487049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487073 : List Nat := [1, 2, 3, 3, 2, 2, 1, 6]
def baseStart_487073 : Nat := 118140960795 + 487073 * 2 ^ 59
def prefixEnd_487073 : Nat := 4983230072969 + 3 ^ 40 * 487073 * 2
def baseEnd_487073 : Nat := 74104463059993498769629

theorem tailTrace_487073 : CollatzResearch.WordTrace tailWord_487073 prefixEnd_487073 74104463059993498769629 := by
  unfold tailWord_487073
  simp only [CollatzResearch.WordTrace]
  refine ⟨17765011764425181290777873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11843341176283454193851915 17765011764425181290777873)
  ·
    refine ⟨13323758823318885968083405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17765011764425181290777873 13323758823318885968083405)
    ·
      refine ⟨4996409558744582238031277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13323758823318885968083405 4996409558744582238031277)
      ·
        refine ⟨1873653584529218339261729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4996409558744582238031277 1873653584529218339261729)
        ·
          refine ⟨1405240188396913754446297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1873653584529218339261729 1405240188396913754446297)
          ·
            refine ⟨1053930141297685315834723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1405240188396913754446297 1053930141297685315834723)
            ·
              refine ⟨1580895211946527973752085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053930141297685315834723 1580895211946527973752085)
              ·
                refine ⟨74104463059993498769629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1580895211946527973752085 74104463059993498769629)
                ·
                  rfl

theorem cell20_487073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 6].length) (baseStart_487073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487073 prefixEnd_487073 := by exact prefixLift 487073
  have htrace : WordTrace (prefixWord ++ tailWord_487073) baseStart_487073 baseEnd_487073 := by
    simpa [prefixWord, tailWord_487073, baseEnd_487073] using wordTrace_append hprefix tailTrace_487073
  have hstable : (prefixWord ++ tailWord_487073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487073).length < 2 ^ (prefixWord ++ tailWord_487073).sum := by decide
  have hdescent : baseEnd_487073 < baseStart_487073 := by decide
  rcases family_descends (prefixWord ++ tailWord_487073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487100 : List Nat := [2, 2, 2, 3, 1, 3, 3, 2, 2]
def baseStart_487100 : Nat := 118140960795 + 487100 * 2 ^ 59
def prefixEnd_487100 : Nat := 4983230072969 + 3 ^ 40 * 487100 * 2
def baseEnd_487100 : Nat := 222325712715688402408777

theorem tailTrace_487100 : CollatzResearch.WordTrace tailWord_487100 prefixEnd_487100 222325712715688402408777 := by
  unfold tailWord_487100
  simp only [CollatzResearch.WordTrace]
  refine ⟨8882998267663682451005377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11843997690218243268007169 8882998267663682451005377)
  ·
    refine ⟨6662248700747761838254033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8882998267663682451005377 6662248700747761838254033)
    ·
      refine ⟨4996686525560821378690525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6662248700747761838254033 4996686525560821378690525)
      ·
        refine ⟨1873757447085308017008947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4996686525560821378690525 1873757447085308017008947)
        ·
          refine ⟨2810636170627962025513421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873757447085308017008947 2810636170627962025513421)
          ·
            refine ⟨1053988563985485759567533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2810636170627962025513421 1053988563985485759567533)
            ·
              refine ⟨395245711494557159837825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1053988563985485759567533 395245711494557159837825)
              ·
                refine ⟨296434283620917869878369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395245711494557159837825 296434283620917869878369)
                ·
                  refine ⟨222325712715688402408777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296434283620917869878369 222325712715688402408777)
                  ·
                    rfl

theorem cell20_487100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_487100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487100 prefixEnd_487100 := by exact prefixLift 487100
  have htrace : WordTrace (prefixWord ++ tailWord_487100) baseStart_487100 baseEnd_487100 := by
    simpa [prefixWord, tailWord_487100, baseEnd_487100] using wordTrace_append hprefix tailTrace_487100
  have hstable : (prefixWord ++ tailWord_487100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487100).length < 2 ^ (prefixWord ++ tailWord_487100).sum := by decide
  have hdescent : baseEnd_487100 < baseStart_487100 := by decide
  rcases family_descends (prefixWord ++ tailWord_487100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487106 : List Nat := [3, 5, 1, 2, 2, 1, 2, 1, 3]
def baseStart_487106 : Nat := 118140960795 + 487106 * 2 ^ 59
def prefixEnd_487106 : Nat := 4983230072969 + 3 ^ 40 * 487106 * 2
def baseEnd_487106 : Nat := 222328451279179048208753

theorem tailTrace_487106 : CollatzResearch.WordTrace tailWord_487106 prefixEnd_487106 222328451279179048208753 := by
  unfold tailWord_487106
  simp only [CollatzResearch.WordTrace]
  refine ⟨4441553843326406981682293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11844143582203751951152781 4441553843326406981682293)
  ·
    refine ⟨416395672811850654532715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4441553843326406981682293 416395672811850654532715)
    ·
      refine ⟨624593509217775981799073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416395672811850654532715 624593509217775981799073)
      ·
        refine ⟨468445131913331986349305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624593509217775981799073 468445131913331986349305)
        ·
          refine ⟨351333848934998989761979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468445131913331986349305 351333848934998989761979)
          ·
            refine ⟨527000773402498484642969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351333848934998989761979 527000773402498484642969)
            ·
              refine ⟨395250580051873863482227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527000773402498484642969 395250580051873863482227)
              ·
                refine ⟨592875870077810795223341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395250580051873863482227 592875870077810795223341)
                ·
                  refine ⟨222328451279179048208753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 592875870077810795223341 222328451279179048208753)
                  ·
                    rfl

theorem cell20_487106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_487106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487106 prefixEnd_487106 := by exact prefixLift 487106
  have htrace : WordTrace (prefixWord ++ tailWord_487106) baseStart_487106 baseEnd_487106 := by
    simpa [prefixWord, tailWord_487106, baseEnd_487106] using wordTrace_append hprefix tailTrace_487106
  have hstable : (prefixWord ++ tailWord_487106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487106).length < 2 ^ (prefixWord ++ tailWord_487106).sum := by decide
  have hdescent : baseEnd_487106 < baseStart_487106 := by decide
  rcases family_descends (prefixWord ++ tailWord_487106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487110 : List Nat := [6, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_487110 : Nat := 118140960795 + 487110 * 2 ^ 59
def prefixEnd_487110 : Nat := 4983230072969 + 3 ^ 40 * 487110 * 2
def baseEnd_487110 : Nat := 222330276988172812075403

theorem tailTrace_487110 : CollatzResearch.WordTrace tailWord_487110 prefixEnd_487110 222330276988172812075403 := by
  unfold tailWord_487110
  simp only [CollatzResearch.WordTrace]
  refine ⟨555198789540348019058587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11844240843527424406583189 555198789540348019058587)
  ·
    refine ⟨832798184310522028587881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 555198789540348019058587 832798184310522028587881)
    ·
      refine ⟨624598638232891521440911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 832798184310522028587881 624598638232891521440911)
      ·
        refine ⟨936897957349337282161367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624598638232891521440911 936897957349337282161367)
        ·
          refine ⟨1405346936024005923242051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936897957349337282161367 1405346936024005923242051)
          ·
            refine ⟨2108020404036008884863077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405346936024005923242051 2108020404036008884863077)
            ·
              refine ⟨395253825756751665911827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2108020404036008884863077 395253825756751665911827)
              ·
                refine ⟨592880738635127498867741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395253825756751665911827 592880738635127498867741)
                ·
                  refine ⟨222330276988172812075403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 592880738635127498867741 222330276988172812075403)
                  ·
                    rfl

theorem cell20_487110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_487110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487110 prefixEnd_487110 := by exact prefixLift 487110
  have htrace : WordTrace (prefixWord ++ tailWord_487110) baseStart_487110 baseEnd_487110 := by
    simpa [prefixWord, tailWord_487110, baseEnd_487110] using wordTrace_append hprefix tailTrace_487110
  have hstable : (prefixWord ++ tailWord_487110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487110).length < 2 ^ (prefixWord ++ tailWord_487110).sum := by decide
  have hdescent : baseEnd_487110 < baseStart_487110 := by decide
  rcases family_descends (prefixWord ++ tailWord_487110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487159 : List Nat := [1, 1, 3, 1, 1, 1, 8, 2, 2]
def baseStart_487159 : Nat := 118140960795 + 487159 * 2 ^ 59
def prefixEnd_487159 : Nat := 4983230072969 + 3 ^ 40 * 487159 * 2
def baseEnd_487159 : Nat := 222352641923346419441869

theorem tailTrace_487159 : CollatzResearch.WordTrace tailWord_487159 prefixEnd_487159 222352641923346419441869 := by
  unfold tailWord_487159
  simp only [CollatzResearch.WordTrace]
  refine ⟨17768148442113617978408531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11845432294742411985605687 17768148442113617978408531)
  ·
    refine ⟨26652222663170426967612797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17768148442113617978408531 26652222663170426967612797)
    ·
      refine ⟨9994583498688910112854799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26652222663170426967612797 9994583498688910112854799)
      ·
        refine ⟨14991875248033365169282199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9994583498688910112854799 14991875248033365169282199)
        ·
          refine ⟨22487812872050047753923299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14991875248033365169282199 22487812872050047753923299)
          ·
            refine ⟨33731719308075071630884949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22487812872050047753923299 33731719308075071630884949)
            ·
              refine ⟨395293585641504745674433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 33731719308075071630884949 395293585641504745674433)
              ·
                refine ⟨296470189231128559255825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395293585641504745674433 296470189231128559255825)
                ·
                  refine ⟨222352641923346419441869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296470189231128559255825 222352641923346419441869)
                  ·
                    rfl

theorem cell20_487159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 2].length) (baseStart_487159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487159 prefixEnd_487159 := by exact prefixLift 487159
  have htrace : WordTrace (prefixWord ++ tailWord_487159) baseStart_487159 baseEnd_487159 := by
    simpa [prefixWord, tailWord_487159, baseEnd_487159] using wordTrace_append hprefix tailTrace_487159
  have hstable : (prefixWord ++ tailWord_487159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487159).length < 2 ^ (prefixWord ++ tailWord_487159).sum := by decide
  have hdescent : baseEnd_487159 < baseStart_487159 := by decide
  rcases family_descends (prefixWord ++ tailWord_487159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487177 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 7]
def baseStart_487177 : Nat := 118140960795 + 487177 * 2 ^ 59
def prefixEnd_487177 : Nat := 4983230072969 + 3 ^ 40 * 487177 * 2
def baseEnd_487177 : Nat := 222360857613818356841795

theorem tailTrace_487177 : CollatzResearch.WordTrace tailWord_487177 prefixEnd_487177 222360857613818356841795 := by
  unfold tailWord_487177
  simp only [CollatzResearch.WordTrace]
  refine ⟨17768804956048407052563785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11845869970698938035042523 17768804956048407052563785)
  ·
    refine ⟨13326603717036305289422839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17768804956048407052563785 13326603717036305289422839)
    ·
      refine ⟨19989905575554457934134259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13326603717036305289422839 19989905575554457934134259)
      ·
        refine ⟨29984858363331686901201389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19989905575554457934134259 29984858363331686901201389)
        ·
          refine ⟨11244321886249382587950521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29984858363331686901201389 11244321886249382587950521)
          ·
            refine ⟨8433241414687036940962891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11244321886249382587950521 8433241414687036940962891)
            ·
              refine ⟨12649862122030555411444337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8433241414687036940962891 12649862122030555411444337)
              ·
                refine ⟨9487396591522916558583253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12649862122030555411444337 9487396591522916558583253)
                ·
                  refine ⟨222360857613818356841795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9487396591522916558583253 222360857613818356841795)
                  ·
                    rfl

theorem cell20_487177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_487177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487177 prefixEnd_487177 := by exact prefixLift 487177
  have htrace : WordTrace (prefixWord ++ tailWord_487177) baseStart_487177 baseEnd_487177 := by
    simpa [prefixWord, tailWord_487177, baseEnd_487177] using wordTrace_append hprefix tailTrace_487177
  have hstable : (prefixWord ++ tailWord_487177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487177).length < 2 ^ (prefixWord ++ tailWord_487177).sum := by decide
  have hdescent : baseEnd_487177 < baseStart_487177 := by decide
  rcases family_descends (prefixWord ++ tailWord_487177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487215 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 5]
def baseStart_487215 : Nat := 118140960795 + 487215 * 2 ^ 59
def prefixEnd_487215 : Nat := 4983230072969 + 3 ^ 40 * 487215 * 2
def baseEnd_487215 : Nat := 222378201849259113574973

theorem tailTrace_487215 : CollatzResearch.WordTrace tailWord_487215 prefixEnd_487215 222378201849259113574973 := by
  unfold tailWord_487215
  simp only [CollatzResearch.WordTrace]
  refine ⟨17770190929910739542447099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11846793953273826361631399 17770190929910739542447099)
  ·
    refine ⟨26655286394866109313670649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17770190929910739542447099 26655286394866109313670649)
    ·
      refine ⟨19991464796149581985252987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26655286394866109313670649 19991464796149581985252987)
      ·
        refine ⟨29987197194224372977879481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19991464796149581985252987 29987197194224372977879481)
        ·
          refine ⟨22490397895668279733409611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29987197194224372977879481 22490397895668279733409611)
          ·
            refine ⟨33735596843502419600114417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22490397895668279733409611 33735596843502419600114417)
            ·
              refine ⟨25301697632626814700085813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33735596843502419600114417 25301697632626814700085813)
              ·
                refine ⟨2372034153058763878133045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25301697632626814700085813 2372034153058763878133045)
                ·
                  refine ⟨222378201849259113574973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2372034153058763878133045 222378201849259113574973)
                  ·
                    rfl

theorem cell20_487215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_487215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487215 prefixEnd_487215 := by exact prefixLift 487215
  have htrace : WordTrace (prefixWord ++ tailWord_487215) baseStart_487215 baseEnd_487215 := by
    simpa [prefixWord, tailWord_487215, baseEnd_487215] using wordTrace_append hprefix tailTrace_487215
  have hstable : (prefixWord ++ tailWord_487215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487215).length < 2 ^ (prefixWord ++ tailWord_487215).sum := by decide
  have hdescent : baseEnd_487215 < baseStart_487215 := by decide
  rcases family_descends (prefixWord ++ tailWord_487215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487218 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_487218 : Nat := 118140960795 + 487218 * 2 ^ 59
def prefixEnd_487218 : Nat := 4983230072969 + 3 ^ 40 * 487218 * 2
def baseEnd_487218 : Nat := 222379571131004436474961

theorem tailTrace_487218 : CollatzResearch.WordTrace tailWord_487218 prefixEnd_487218 222379571131004436474961 := by
  unfold tailWord_487218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4442575087224967763701577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11846866899266580703204205 4442575087224967763701577)
  ·
    refine ⟨3331931315418725822776183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4442575087224967763701577 3331931315418725822776183)
    ·
      refine ⟨4997896973128088734164275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3331931315418725822776183 4997896973128088734164275)
      ·
        refine ⟨7496845459692133101246413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4997896973128088734164275 7496845459692133101246413)
        ·
          refine ⟨2811317047384549912967405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7496845459692133101246413 2811317047384549912967405)
          ·
            refine ⟨1054243892769206217362777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2811317047384549912967405 1054243892769206217362777)
            ·
              refine ⟨790682919576904663022083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054243892769206217362777 790682919576904663022083)
              ·
                refine ⟨1186024379365356994533125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790682919576904663022083 1186024379365356994533125)
                ·
                  refine ⟨222379571131004436474961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1186024379365356994533125 222379571131004436474961)
                  ·
                    rfl

theorem cell20_487218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_487218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487218 prefixEnd_487218 := by exact prefixLift 487218
  have htrace : WordTrace (prefixWord ++ tailWord_487218) baseStart_487218 baseEnd_487218 := by
    simpa [prefixWord, tailWord_487218, baseEnd_487218] using wordTrace_append hprefix tailTrace_487218
  have hstable : (prefixWord ++ tailWord_487218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487218).length < 2 ^ (prefixWord ++ tailWord_487218).sum := by decide
  have hdescent : baseEnd_487218 < baseStart_487218 := by decide
  rcases family_descends (prefixWord ++ tailWord_487218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487238 : List Nat := [6, 1, 1, 2, 1, 3, 2, 4]
def baseStart_487238 : Nat := 118140960795 + 487238 * 2 ^ 59
def prefixEnd_487238 : Nat := 4983230072969 + 3 ^ 40 * 487238 * 2
def baseEnd_487238 : Nat := 74129566558657751936071

theorem tailTrace_487238 : CollatzResearch.WordTrace tailWord_487238 prefixEnd_487238 74129566558657751936071 := by
  unfold tailWord_487238
  simp only [CollatzResearch.WordTrace]
  refine ⟨555344681525856702204199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11847353205884942980356245 555344681525856702204199)
  ·
    refine ⟨833017022288785053306299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 555344681525856702204199 833017022288785053306299)
    ·
      refine ⟨1249525533433177579959449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 833017022288785053306299 1249525533433177579959449)
      ·
        refine ⟨937144150074883184969587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1249525533433177579959449 937144150074883184969587)
        ·
          refine ⟨1405716225112324777454381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 937144150074883184969587 1405716225112324777454381)
          ·
            refine ⟨527143584417121791545393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1405716225112324777454381 527143584417121791545393)
            ·
              refine ⟨395357688312841343659045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527143584417121791545393 395357688312841343659045)
              ·
                refine ⟨74129566558657751936071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 395357688312841343659045 74129566558657751936071)
                ·
                  rfl

theorem cell20_487238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_487238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487238 prefixEnd_487238 := by exact prefixLift 487238
  have htrace : WordTrace (prefixWord ++ tailWord_487238) baseStart_487238 baseEnd_487238 := by
    simpa [prefixWord, tailWord_487238, baseEnd_487238] using wordTrace_append hprefix tailTrace_487238
  have hstable : (prefixWord ++ tailWord_487238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487238).length < 2 ^ (prefixWord ++ tailWord_487238).sum := by decide
  have hdescent : baseEnd_487238 < baseStart_487238 := by decide
  rcases family_descends (prefixWord ++ tailWord_487238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487239 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 4]
def baseStart_487239 : Nat := 118140960795 + 487239 * 2 ^ 59
def prefixEnd_487239 : Nat := 4983230072969 + 3 ^ 40 * 487239 * 2
def baseEnd_487239 : Nat := 222389156103221696774875

theorem tailTrace_487239 : CollatzResearch.WordTrace tailWord_487239 prefixEnd_487239 222389156103221696774875 := by
  unfold tailWord_487239
  simp only [CollatzResearch.WordTrace]
  refine ⟨17771066281823791641320771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11847377521215861094213847 17771066281823791641320771)
  ·
    refine ⟨26656599422735687461981157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17771066281823791641320771 26656599422735687461981157)
    ·
      refine ⟨4998112391762941399121467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26656599422735687461981157 4998112391762941399121467)
      ·
        refine ⟨7497168587644412098682201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4998112391762941399121467 7497168587644412098682201)
        ·
          refine ⟨5622876440733309074011651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7497168587644412098682201 5622876440733309074011651)
          ·
            refine ⟨8434314661099963611017477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5622876440733309074011651 8434314661099963611017477)
            ·
              refine ⟨1581433998956243177065777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8434314661099963611017477 1581433998956243177065777)
              ·
                refine ⟨1186075499217182382799333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1581433998956243177065777 1186075499217182382799333)
                ·
                  refine ⟨222389156103221696774875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1186075499217182382799333 222389156103221696774875)
                  ·
                    rfl

theorem cell20_487239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_487239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487239 prefixEnd_487239 := by exact prefixLift 487239
  have htrace : WordTrace (prefixWord ++ tailWord_487239) baseStart_487239 baseEnd_487239 := by
    simpa [prefixWord, tailWord_487239, baseEnd_487239] using wordTrace_append hprefix tailTrace_487239
  have hstable : (prefixWord ++ tailWord_487239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487239).length < 2 ^ (prefixWord ++ tailWord_487239).sum := by decide
  have hdescent : baseEnd_487239 < baseStart_487239 := by decide
  rcases family_descends (prefixWord ++ tailWord_487239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487252 : List Nat := [2, 4, 1, 1, 3, 3, 1, 3, 2]
def baseStart_487252 : Nat := 118140960795 + 487252 * 2 ^ 59
def prefixEnd_487252 : Nat := 4983230072969 + 3 ^ 40 * 487252 * 2
def baseEnd_487252 : Nat := 222395089657451429341489

theorem tailTrace_487252 : CollatzResearch.WordTrace tailWord_487252 prefixEnd_487252 222395089657451429341489 := by
  unfold tailWord_487252
  simp only [CollatzResearch.WordTrace]
  refine ⟨8885770215388347430772005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11847693620517796574362673 8885770215388347430772005)
  ·
    refine ⟨1666081915385315143269751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8885770215388347430772005 1666081915385315143269751)
    ·
      refine ⟨2499122873077972714904627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1666081915385315143269751 2499122873077972714904627)
      ·
        refine ⟨3748684309616959072356941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2499122873077972714904627 3748684309616959072356941)
        ·
          refine ⟨1405756616106359652133853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3748684309616959072356941 1405756616106359652133853)
          ·
            refine ⟨527158731039884869550195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1405756616106359652133853 527158731039884869550195)
            ·
              refine ⟨790738096559827304325293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527158731039884869550195 790738096559827304325293)
              ·
                refine ⟨296526786209935239121985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 790738096559827304325293 296526786209935239121985)
                ·
                  refine ⟨222395089657451429341489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296526786209935239121985 222395089657451429341489)
                  ·
                    rfl

theorem cell20_487252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_487252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_487252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_487252 prefixEnd_487252 := by exact prefixLift 487252
  have htrace : WordTrace (prefixWord ++ tailWord_487252) baseStart_487252 baseEnd_487252 := by
    simpa [prefixWord, tailWord_487252, baseEnd_487252] using wordTrace_append hprefix tailTrace_487252
  have hstable : (prefixWord ++ tailWord_487252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487252).length < 2 ^ (prefixWord ++ tailWord_487252).sum := by decide
  have hdescent : baseEnd_487252 < baseStart_487252 := by decide
  rcases family_descends (prefixWord ++ tailWord_487252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
