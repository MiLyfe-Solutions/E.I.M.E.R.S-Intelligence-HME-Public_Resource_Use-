import V185TrunkScan23Chunk0770

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4559607 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 7, 1, 3]
def baseStart_4559607 : Nat := 118140960795 + 4559607 * 2 ^ 59
def prefixEnd_4559607 : Nat := 4983230072969 + 3 ^ 40 * 4559607 * 2
def baseEnd_4559607 : Nat := 2341269986605047250343255

theorem tailTrace_4559607 : CollatzResearch.WordTrace tailWord_4559607 prefixEnd_4559607 2341269986605047250343255 := by
  unfold tailWord_4559607
  simp only [CollatzResearch.WordTrace]
  refine ⟨166302529592330032723733075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110868353061553355149155383 166302529592330032723733075)
  ·
    refine ⟨249453794388495049085599613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166302529592330032723733075 249453794388495049085599613)
    ·
      refine ⟨93545172895685643407099855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249453794388495049085599613 93545172895685643407099855)
      ·
        refine ⟨140317759343528465110649783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93545172895685643407099855 140317759343528465110649783)
        ·
          refine ⟨210476639015292697665974675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140317759343528465110649783 210476639015292697665974675)
          ·
            refine ⟨315714958522939046498962013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210476639015292697665974675 315714958522939046498962013)
            ·
              refine ⟨118393109446102142437110755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 315714958522939046498962013 118393109446102142437110755)
              ·
                refine ⟨177589664169153213655666133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118393109446102142437110755 177589664169153213655666133)
                ·
                  refine ⟨4162257753964528445054675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 177589664169153213655666133 4162257753964528445054675)
                  ·
                    refine ⟨6243386630946792667582013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4162257753964528445054675 6243386630946792667582013)
                    ·
                      refine ⟨2341269986605047250343255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6243386630946792667582013 2341269986605047250343255)
                      ·
                        rfl

theorem cell23_4559607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 1, 3].length) (baseStart_4559607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559607 prefixEnd_4559607 := by exact prefixLift 4559607
  have htrace : WordTrace (prefixWord ++ tailWord_4559607) baseStart_4559607 baseEnd_4559607 := by
    simpa [prefixWord, tailWord_4559607, baseEnd_4559607] using wordTrace_append hprefix tailTrace_4559607
  have hstable : (prefixWord ++ tailWord_4559607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559607).length < 2 ^ (prefixWord ++ tailWord_4559607).sum := by decide
  have hdescent : baseEnd_4559607 < baseStart_4559607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559614 : List Nat := [4, 2, 2, 1, 2, 1, 3, 2, 6]
def baseStart_4559614 : Nat := 118140960795 + 4559614 * 2 ^ 59
def prefixEnd_4559614 : Nat := 4983230072969 + 3 ^ 40 * 4559614 * 2
def baseEnd_4559614 : Nat := 260141508996625413661747

theorem tailTrace_4559614 : CollatzResearch.WordTrace tailWord_4559614 prefixEnd_4559614 260141508996625413661747 := by
  unfold tailWord_4559614
  simp only [CollatzResearch.WordTrace]
  refine ⟨20787848112913084114904737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110868523268869781946158597 20787848112913084114904737)
  ·
    refine ⟨15590886084684813086178553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20787848112913084114904737 15590886084684813086178553)
    ·
      refine ⟨11693164563513609814633915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15590886084684813086178553 11693164563513609814633915)
      ·
        refine ⟨17539746845270414721950873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11693164563513609814633915 17539746845270414721950873)
        ·
          refine ⟨13154810133952811041463155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17539746845270414721950873 13154810133952811041463155)
          ·
            refine ⟨19732215200929216562194733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13154810133952811041463155 19732215200929216562194733)
            ·
              refine ⟨7399580700348456210823025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19732215200929216562194733 7399580700348456210823025)
              ·
                refine ⟨5549685525261342158117269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7399580700348456210823025 5549685525261342158117269)
                ·
                  refine ⟨260141508996625413661747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5549685525261342158117269 260141508996625413661747)
                  ·
                    rfl

theorem cell23_4559614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_4559614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559614 prefixEnd_4559614 := by exact prefixLift 4559614
  have htrace : WordTrace (prefixWord ++ tailWord_4559614) baseStart_4559614 baseEnd_4559614 := by
    simpa [prefixWord, tailWord_4559614, baseEnd_4559614] using wordTrace_append hprefix tailTrace_4559614
  have hstable : (prefixWord ++ tailWord_4559614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559614).length < 2 ^ (prefixWord ++ tailWord_4559614).sum := by decide
  have hdescent : baseEnd_4559614 < baseStart_4559614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559624 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 3, 1, 3]
def baseStart_4559624 : Nat := 118140960795 + 4559624 * 2 ^ 59
def prefixEnd_4559624 : Nat := 4983230072969 + 3 ^ 40 * 4559624 * 2
def baseEnd_4559624 : Nat := 2341278715776173683830677

theorem tailTrace_4559624 : CollatzResearch.WordTrace tailWord_4559624 prefixEnd_4559624 2341278715776173683830677 := by
  unfold tailWord_4559624
  simp only [CollatzResearch.WordTrace]
  refine ⟨83151574816634222313550963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110868766422178963084734617 83151574816634222313550963)
  ·
    refine ⟨124727362224951333470326445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83151574816634222313550963 124727362224951333470326445)
    ·
      refine ⟨46772760834356750051372417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124727362224951333470326445 46772760834356750051372417)
      ·
        refine ⟨35079570625767562538529313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46772760834356750051372417 35079570625767562538529313)
        ·
          refine ⟨26309677969325671903896985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35079570625767562538529313 26309677969325671903896985)
          ·
            refine ⟨19732258476994253927922739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26309677969325671903896985 19732258476994253927922739)
            ·
              refine ⟨29598387715491380891884109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19732258476994253927922739 29598387715491380891884109)
              ·
                refine ⟨11099395393309267834456541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29598387715491380891884109 11099395393309267834456541)
                ·
                  refine ⟨4162273272490975437921203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11099395393309267834456541 4162273272490975437921203)
                  ·
                    refine ⟨6243409908736463156881805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4162273272490975437921203 6243409908736463156881805)
                    ·
                      refine ⟨2341278715776173683830677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6243409908736463156881805 2341278715776173683830677)
                      ·
                        rfl

theorem cell23_4559624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_4559624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559624 prefixEnd_4559624 := by exact prefixLift 4559624
  have htrace : WordTrace (prefixWord ++ tailWord_4559624) baseStart_4559624 baseEnd_4559624 := by
    simpa [prefixWord, tailWord_4559624, baseEnd_4559624] using wordTrace_append hprefix tailTrace_4559624
  have hstable : (prefixWord ++ tailWord_4559624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559624).length < 2 ^ (prefixWord ++ tailWord_4559624).sum := by decide
  have hdescent : baseEnd_4559624 < baseStart_4559624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559644 : List Nat := [2, 2, 3, 1, 1, 4, 2, 2, 1, 5]
def baseStart_4559644 : Nat := 118140960795 + 4559644 * 2 ^ 59
def prefixEnd_4559644 : Nat := 4983230072969 + 3 ^ 40 * 4559644 * 2
def baseEnd_4559644 : Nat := 780429661796421201860195

theorem tailTrace_4559644 : CollatzResearch.WordTrace tailWord_4559644 prefixEnd_4559644 780429661796421201860195 := by
  unfold tailWord_4559644
  simp only [CollatzResearch.WordTrace]
  refine ⟨83151939546597994021414993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110869252728797325361886657 83151939546597994021414993)
  ·
    refine ⟨62363954659948495516061245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83151939546597994021414993 62363954659948495516061245)
    ·
      refine ⟨23386482997480685818522967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62363954659948495516061245 23386482997480685818522967)
      ·
        refine ⟨35079724496221028727784451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23386482997480685818522967 35079724496221028727784451)
        ·
          refine ⟨52619586744331543091676677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35079724496221028727784451 52619586744331543091676677)
          ·
            refine ⟨9866172514562164329689377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52619586744331543091676677 9866172514562164329689377)
            ·
              refine ⟨7399629385921623247267033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9866172514562164329689377 7399629385921623247267033)
              ·
                refine ⟨5549722039441217435450275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7399629385921623247267033 5549722039441217435450275)
                ·
                  refine ⟨8324583059161826153175413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5549722039441217435450275 8324583059161826153175413)
                  ·
                    refine ⟨780429661796421201860195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8324583059161826153175413 780429661796421201860195)
                    ·
                      rfl

theorem cell23_4559644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_4559644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559644 prefixEnd_4559644 := by exact prefixLift 4559644
  have htrace : WordTrace (prefixWord ++ tailWord_4559644) baseStart_4559644 baseEnd_4559644 := by
    simpa [prefixWord, tailWord_4559644, baseEnd_4559644] using wordTrace_append hprefix tailTrace_4559644
  have hstable : (prefixWord ++ tailWord_4559644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559644).length < 2 ^ (prefixWord ++ tailWord_4559644).sum := by decide
  have hdescent : baseEnd_4559644 < baseStart_4559644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559664 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 5, 2, 2]
def baseStart_4559664 : Nat := 118140960795 + 4559664 * 2 ^ 59
def prefixEnd_4559664 : Nat := 4983230072969 + 3 ^ 40 * 4559664 * 2
def baseEnd_4559664 : Nat := 2341299255002353527330493

theorem tailTrace_4559664 : CollatzResearch.WordTrace tailWord_4559664 prefixEnd_4559664 2341299255002353527330493 := by
  unfold tailWord_4559664
  simp only [CollatzResearch.WordTrace]
  refine ⟨83152304276561765729279023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110869739035415687639038697 83152304276561765729279023)
  ·
    refine ⟨124728456414842648593918535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83152304276561765729279023 124728456414842648593918535)
    ·
      refine ⟨187092684622263972890877803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124728456414842648593918535 187092684622263972890877803)
      ·
        refine ⟨280639026933395959336316705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187092684622263972890877803 280639026933395959336316705)
        ·
          refine ⟨210479270200046969502237529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280639026933395959336316705 210479270200046969502237529)
          ·
            refine ⟨157859452650035227126678147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210479270200046969502237529 157859452650035227126678147)
            ·
              refine ⟨236789178975052840690017221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157859452650035227126678147 236789178975052840690017221)
              ·
                refine ⟨44397971057822407629378229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 236789178975052840690017221 44397971057822407629378229)
                ·
                  refine ⟨4162309786670850715254209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44397971057822407629378229 4162309786670850715254209)
                  ·
                    refine ⟨3121732340003138036440657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4162309786670850715254209 3121732340003138036440657)
                    ·
                      refine ⟨2341299255002353527330493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3121732340003138036440657 2341299255002353527330493)
                      ·
                        rfl

theorem cell23_4559664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 5, 2, 2].length) (baseStart_4559664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559664 prefixEnd_4559664 := by exact prefixLift 4559664
  have htrace : WordTrace (prefixWord ++ tailWord_4559664) baseStart_4559664 baseEnd_4559664 := by
    simpa [prefixWord, tailWord_4559664, baseEnd_4559664] using wordTrace_append hprefix tailTrace_4559664
  have hstable : (prefixWord ++ tailWord_4559664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559664).length < 2 ^ (prefixWord ++ tailWord_4559664).sum := by decide
  have hdescent : baseEnd_4559664 < baseStart_4559664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559667 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 5]
def baseStart_4559667 : Nat := 118140960795 + 4559667 * 2 ^ 59
def prefixEnd_4559667 : Nat := 4983230072969 + 3 ^ 40 * 4559667 * 2
def baseEnd_4559667 : Nat := 2341300795444317015592979

theorem tailTrace_4559667 : CollatzResearch.WordTrace tailWord_4559667 prefixEnd_4559667 2341300795444317015592979 := by
  unfold tailWord_4559667
  simp only [CollatzResearch.WordTrace]
  refine ⟨166304717972112662970917255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110869811981408441980611503 166304717972112662970917255)
  ·
    refine ⟨249457076958168994456375883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166304717972112662970917255 249457076958168994456375883)
    ·
      refine ⟨374185615437253491684563825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249457076958168994456375883 374185615437253491684563825)
      ·
        refine ⟨280639211577940118763422869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374185615437253491684563825 280639211577940118763422869)
        ·
          refine ⟨13154963042715943067035447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 280639211577940118763422869 13154963042715943067035447)
          ·
            refine ⟨19732444564073914600553171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13154963042715943067035447 19732444564073914600553171)
            ·
              refine ⟨29598666846110871900829757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19732444564073914600553171 29598666846110871900829757)
              ·
                refine ⟨11099500067291576962811159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29598666846110871900829757 11099500067291576962811159)
                ·
                  refine ⟨16649250100937365444216739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11099500067291576962811159 16649250100937365444216739)
                  ·
                    refine ⟨24973875151406048166325109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16649250100937365444216739 24973875151406048166325109)
                    ·
                      refine ⟨2341300795444317015592979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24973875151406048166325109 2341300795444317015592979)
                      ·
                        rfl

theorem cell23_4559667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 5].length) (baseStart_4559667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559667 prefixEnd_4559667 := by exact prefixLift 4559667
  have htrace : WordTrace (prefixWord ++ tailWord_4559667) baseStart_4559667 baseEnd_4559667 := by
    simpa [prefixWord, tailWord_4559667, baseEnd_4559667] using wordTrace_append hprefix tailTrace_4559667
  have hstable : (prefixWord ++ tailWord_4559667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559667).length < 2 ^ (prefixWord ++ tailWord_4559667).sum := by decide
  have hdescent : baseEnd_4559667 < baseStart_4559667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559668 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_4559668 : Nat := 118140960795 + 4559668 * 2 ^ 59
def prefixEnd_4559668 : Nat := 4983230072969 + 3 ^ 40 * 4559668 * 2
def baseEnd_4559668 : Nat := 2341301308924971511680475

theorem tailTrace_4559668 : CollatzResearch.WordTrace tailWord_4559668 prefixEnd_4559668 2341301308924971511680475 := by
  unfold tailWord_4559668
  simp only [CollatzResearch.WordTrace]
  refine ⟨83152377222554520070851829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110869836296739360094469105 83152377222554520070851829)
  ·
    refine ⟨7795535364614486256642359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83152377222554520070851829 7795535364614486256642359)
    ·
      refine ⟨11693303046921729384963539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7795535364614486256642359 11693303046921729384963539)
      ·
        refine ⟨17539954570382594077445309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11693303046921729384963539 17539954570382594077445309)
        ·
          refine ⟨6577482963893472779041991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17539954570382594077445309 6577482963893472779041991)
          ·
            refine ⟨9866224445840209168562987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6577482963893472779041991 9866224445840209168562987)
            ·
              refine ⟨14799336668760313752844481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9866224445840209168562987 14799336668760313752844481)
              ·
                refine ⟨11099502501570235314633361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14799336668760313752844481 11099502501570235314633361)
                ·
                  refine ⟨8324626876177676485975021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11099502501570235314633361 8324626876177676485975021)
                  ·
                    refine ⟨3121735078566628682240633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8324626876177676485975021 3121735078566628682240633)
                    ·
                      refine ⟨2341301308924971511680475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3121735078566628682240633 2341301308924971511680475)
                      ·
                        rfl

theorem cell23_4559668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_4559668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559668 prefixEnd_4559668 := by exact prefixLift 4559668
  have htrace : WordTrace (prefixWord ++ tailWord_4559668) baseStart_4559668 baseEnd_4559668 := by
    simpa [prefixWord, tailWord_4559668, baseEnd_4559668] using wordTrace_append hprefix tailTrace_4559668
  have hstable : (prefixWord ++ tailWord_4559668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559668).length < 2 ^ (prefixWord ++ tailWord_4559668).sum := by decide
  have hdescent : baseEnd_4559668 < baseStart_4559668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559734 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_4559734 : Nat := 118140960795 + 4559734 * 2 ^ 59
def prefixEnd_4559734 : Nat := 4983230072969 + 3 ^ 40 * 4559734 * 2
def baseEnd_4559734 : Nat := 780445066216056084485057

theorem tailTrace_4559734 : CollatzResearch.WordTrace tailWord_4559734 prefixEnd_4559734 780445066216056084485057 := by
  unfold tailWord_4559734
  simp only [CollatzResearch.WordTrace]
  refine ⟨10394197603929370838350391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110871441108579955609070837 10394197603929370838350391)
  ·
    refine ⟨15591296405894056257525587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10394197603929370838350391 15591296405894056257525587)
    ·
      refine ⟨23386944608841084386288381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15591296405894056257525587 23386944608841084386288381)
      ·
        refine ⟨8770104228315406644858143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23386944608841084386288381 8770104228315406644858143)
        ·
          refine ⟨13155156342473109967287215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8770104228315406644858143 13155156342473109967287215)
          ·
            refine ⟨19732734513709664950930823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13155156342473109967287215 19732734513709664950930823)
            ·
              refine ⟨29599101770564497426396235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19732734513709664950930823 29599101770564497426396235)
              ·
                refine ⟨44398652655846746139594353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29599101770564497426396235 44398652655846746139594353)
                ·
                  refine ⟨33298989491885059604695765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44398652655846746139594353 33298989491885059604695765)
                  ·
                    refine ⟨780445066216056084485057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33298989491885059604695765 780445066216056084485057)
                    ·
                      rfl

theorem cell23_4559734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_4559734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559734 prefixEnd_4559734 := by exact prefixLift 4559734
  have htrace : WordTrace (prefixWord ++ tailWord_4559734) baseStart_4559734 baseEnd_4559734 := by
    simpa [prefixWord, tailWord_4559734, baseEnd_4559734] using wordTrace_append hprefix tailTrace_4559734
  have hstable : (prefixWord ++ tailWord_4559734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559734).length < 2 ^ (prefixWord ++ tailWord_4559734).sum := by decide
  have hdescent : baseEnd_4559734 < baseStart_4559734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559737 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 2, 3, 4]
def baseStart_4559737 : Nat := 118140960795 + 4559737 * 2 ^ 59
def prefixEnd_4559737 : Nat := 4983230072969 + 3 ^ 40 * 4559737 * 2
def baseEnd_4559737 : Nat := 2341336739090131741717657

theorem tailTrace_4559737 : CollatzResearch.WordTrace tailWord_4559737 prefixEnd_4559737 2341336739090131741717657 := by
  unfold tailWord_4559737
  simp only [CollatzResearch.WordTrace]
  refine ⟨166307271081859064925965465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110871514054572709950643643 166307271081859064925965465)
  ·
    refine ⟨124730453311394298694474099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166307271081859064925965465 124730453311394298694474099)
    ·
      refine ⟨187095679967091448041711149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124730453311394298694474099 187095679967091448041711149)
      ·
        refine ⟨70160879987659293015641681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187095679967091448041711149 70160879987659293015641681)
        ·
          refine ⟨52620659990744469761731261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70160879987659293015641681 52620659990744469761731261)
          ·
            refine ⟨19732747496529176160649223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52620659990744469761731261 19732747496529176160649223)
            ·
              refine ⟨29599121244793764240973835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19732747496529176160649223 29599121244793764240973835)
              ·
                refine ⟨44398681867190646361460753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29599121244793764240973835 44398681867190646361460753)
                ·
                  refine ⟨33299011400392984771095565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44398681867190646361460753 33299011400392984771095565)
                  ·
                    refine ⟨12487129275147369289160837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33299011400392984771095565 12487129275147369289160837)
                    ·
                      refine ⟨2341336739090131741717657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12487129275147369289160837 2341336739090131741717657)
                      ·
                        rfl

theorem cell23_4559737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_4559737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559737 prefixEnd_4559737 := by exact prefixLift 4559737
  have htrace : WordTrace (prefixWord ++ tailWord_4559737) baseStart_4559737 baseEnd_4559737 := by
    simpa [prefixWord, tailWord_4559737, baseEnd_4559737] using wordTrace_append hprefix tailTrace_4559737
  have hstable : (prefixWord ++ tailWord_4559737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559737).length < 2 ^ (prefixWord ++ tailWord_4559737).sum := by decide
  have hdescent : baseEnd_4559737 < baseStart_4559737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559747 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 2, 6]
def baseStart_4559747 : Nat := 118140960795 + 4559747 * 2 ^ 59
def prefixEnd_4559747 : Nat := 4983230072969 + 3 ^ 40 * 4559747 * 2
def baseEnd_4559747 : Nat := 780447291298892234197537

theorem tailTrace_4559747 : CollatzResearch.WordTrace tailWord_4559747 prefixEnd_4559747 780447291298892234197537 := by
  unfold tailWord_4559747
  simp only [CollatzResearch.WordTrace]
  refine ⟨166307635811822836633829495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110871757207881891089219663 166307635811822836633829495)
  ·
    refine ⟨249461453717734254950744243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166307635811822836633829495 249461453717734254950744243)
    ·
      refine ⟨374192180576601382426116365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249461453717734254950744243 374192180576601382426116365)
      ·
        refine ⟨140322067716225518409793637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 374192180576601382426116365 140322067716225518409793637)
        ·
          refine ⟨26310387696792284701836307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140322067716225518409793637 26310387696792284701836307)
          ·
            refine ⟨39465581545188427052754461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26310387696792284701836307 39465581545188427052754461)
            ·
              refine ⟨14799593079445660144782923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39465581545188427052754461 14799593079445660144782923)
              ·
                refine ⟨22199389619168490217174385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14799593079445660144782923 22199389619168490217174385)
                ·
                  refine ⟨16649542214376367662880789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22199389619168490217174385 16649542214376367662880789)
                  ·
                    refine ⟨780447291298892234197537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16649542214376367662880789 780447291298892234197537)
                    ·
                      rfl

theorem cell23_4559747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 6].length) (baseStart_4559747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559747 prefixEnd_4559747 := by exact prefixLift 4559747
  have htrace : WordTrace (prefixWord ++ tailWord_4559747) baseStart_4559747 baseEnd_4559747 := by
    simpa [prefixWord, tailWord_4559747, baseEnd_4559747] using wordTrace_append hprefix tailTrace_4559747
  have hstable : (prefixWord ++ tailWord_4559747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559747).length < 2 ^ (prefixWord ++ tailWord_4559747).sum := by decide
  have hdescent : baseEnd_4559747 < baseStart_4559747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559767 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 4]
def baseStart_4559767 : Nat := 118140960795 + 4559767 * 2 ^ 59
def prefixEnd_4559767 : Nat := 4983230072969 + 3 ^ 40 * 4559767 * 2
def baseEnd_4559767 : Nat := 2341352143509766624342519

theorem tailTrace_4559767 : CollatzResearch.WordTrace tailWord_4559767 prefixEnd_4559767 2341352143509766624342519 := by
  unfold tailWord_4559767
  simp only [CollatzResearch.WordTrace]
  refine ⟨166308365271750380049557555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110872243514500253366371703 166308365271750380049557555)
  ·
    refine ⟨249462547907625570074336333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166308365271750380049557555 249462547907625570074336333)
    ·
      refine ⟨93548455465359588777876125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249462547907625570074336333 93548455465359588777876125)
      ·
        refine ⟨35080670799509845791703547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93548455465359588777876125 35080670799509845791703547)
        ·
          refine ⟨52621006199264768687555321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35080670799509845791703547 52621006199264768687555321)
          ·
            refine ⟨39465754649448576515666491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52621006199264768687555321 39465754649448576515666491)
            ·
              refine ⟨59198631974172864773499737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39465754649448576515666491 59198631974172864773499737)
              ·
                refine ⟨44398973980629648580124803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59198631974172864773499737 44398973980629648580124803)
                ·
                  refine ⟨66598460970944472870187205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44398973980629648580124803 66598460970944472870187205)
                  ·
                    refine ⟨12487211432052088663160101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66598460970944472870187205 12487211432052088663160101)
                    ·
                      refine ⟨2341352143509766624342519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12487211432052088663160101 2341352143509766624342519)
                      ·
                        rfl

theorem cell23_4559767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_4559767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559767 prefixEnd_4559767 := by exact prefixLift 4559767
  have htrace : WordTrace (prefixWord ++ tailWord_4559767) baseStart_4559767 baseEnd_4559767 := by
    simpa [prefixWord, tailWord_4559767, baseEnd_4559767] using wordTrace_append hprefix tailTrace_4559767
  have hstable : (prefixWord ++ tailWord_4559767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559767).length < 2 ^ (prefixWord ++ tailWord_4559767).sum := by decide
  have hdescent : baseEnd_4559767 < baseStart_4559767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559775 : List Nat := [1, 1, 2, 5, 2, 3, 2, 1, 1, 3, 2]
def baseStart_4559775 : Nat := 118140960795 + 4559775 * 2 ^ 59
def prefixEnd_4559775 : Nat := 4983230072969 + 3 ^ 40 * 4559775 * 2
def baseEnd_4559775 : Nat := 2341356251355002593042483

theorem tailTrace_4559775 : CollatzResearch.WordTrace tailWord_4559775 prefixEnd_4559775 2341356251355002593042483 := by
  unfold tailWord_4559775
  simp only [CollatzResearch.WordTrace]
  refine ⟨166308657055721397415848779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110872438037147598277232519 166308657055721397415848779)
  ·
    refine ⟨249462985583582096123773169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166308657055721397415848779 249462985583582096123773169)
    ·
      refine ⟨187097239187686572092829877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249462985583582096123773169 187097239187686572092829877)
      ·
        refine ⟨17540366173845616133702801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 187097239187686572092829877 17540366173845616133702801)
        ·
          refine ⟨13155274630384212100277101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17540366173845616133702801 13155274630384212100277101)
          ·
            refine ⟨4933227986394079537603913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13155274630384212100277101 4933227986394079537603913)
            ·
              refine ⟨3699920989795559653202935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4933227986394079537603913 3699920989795559653202935)
              ·
                refine ⟨5549881484693339479804403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3699920989795559653202935 5549881484693339479804403)
                ·
                  refine ⟨8324822227040009219706605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5549881484693339479804403 8324822227040009219706605)
                  ·
                    refine ⟨3121808335140003457389977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8324822227040009219706605 3121808335140003457389977)
                    ·
                      refine ⟨2341356251355002593042483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3121808335140003457389977 2341356251355002593042483)
                      ·
                        rfl

theorem cell23_4559775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_4559775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559775 prefixEnd_4559775 := by exact prefixLift 4559775
  have htrace : WordTrace (prefixWord ++ tailWord_4559775) baseStart_4559775 baseEnd_4559775 := by
    simpa [prefixWord, tailWord_4559775, baseEnd_4559775] using wordTrace_append hprefix tailTrace_4559775
  have hstable : (prefixWord ++ tailWord_4559775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559775).length < 2 ^ (prefixWord ++ tailWord_4559775).sum := by decide
  have hdescent : baseEnd_4559775 < baseStart_4559775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559787 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 3]
def baseStart_4559787 : Nat := 118140960795 + 4559787 * 2 ^ 59
def prefixEnd_4559787 : Nat := 4983230072969 + 3 ^ 40 * 4559787 * 2
def baseEnd_4559787 : Nat := 2341362413122856546092427

theorem tailTrace_4559787 : CollatzResearch.WordTrace tailWord_4559787 prefixEnd_4559787 2341362413122856546092427 := by
  unfold tailWord_4559787
  simp only [CollatzResearch.WordTrace]
  refine ⟨166309094731677923465285615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110872729821118615643523743 166309094731677923465285615)
  ·
    refine ⟨249463642097516885197928423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166309094731677923465285615 249463642097516885197928423)
    ·
      refine ⟨374195463146275327796892635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249463642097516885197928423 374195463146275327796892635)
      ·
        refine ⟨561293194719412991695338953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374195463146275327796892635 561293194719412991695338953)
        ·
          refine ⟨420969896039559743771504215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 561293194719412991695338953 420969896039559743771504215)
          ·
            refine ⟨631454844059339615657256323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420969896039559743771504215 631454844059339615657256323)
            ·
              refine ⟨947182266089009423485884485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631454844059339615657256323 947182266089009423485884485)
              ·
                refine ⟨177596674891689266903603341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 947182266089009423485884485 177596674891689266903603341)
                ·
                  refine ⟨66598753084383475088851253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177596674891689266903603341 66598753084383475088851253)
                  ·
                    refine ⟨6243633101660950789579805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66598753084383475088851253 6243633101660950789579805)
                    ·
                      refine ⟨2341362413122856546092427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6243633101660950789579805 2341362413122856546092427)
                      ·
                        rfl

theorem cell23_4559787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 3].length) (baseStart_4559787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559787 prefixEnd_4559787 := by exact prefixLift 4559787
  have htrace : WordTrace (prefixWord ++ tailWord_4559787) baseStart_4559787 baseEnd_4559787 := by
    simpa [prefixWord, tailWord_4559787, baseEnd_4559787] using wordTrace_append hprefix tailTrace_4559787
  have hstable : (prefixWord ++ tailWord_4559787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559787).length < 2 ^ (prefixWord ++ tailWord_4559787).sum := by decide
  have hdescent : baseEnd_4559787 < baseStart_4559787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559805 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 1, 4, 2]
def baseStart_4559805 : Nat := 118140960795 + 4559805 * 2 ^ 59
def prefixEnd_4559805 : Nat := 4983230072969 + 3 ^ 40 * 4559805 * 2
def baseEnd_4559805 : Nat := 2341371655774637475667345

theorem tailTrace_4559805 : CollatzResearch.WordTrace tailWord_4559805 prefixEnd_4559805 2341371655774637475667345 := by
  unfold tailWord_4559805
  simp only [CollatzResearch.WordTrace]
  refine ⟨166309751245612712539440869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110873167497075141692960579 166309751245612712539440869)
  ·
    refine ⟨31183078358552383601145163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166309751245612712539440869 31183078358552383601145163)
    ·
      refine ⟨46774617537828575401717745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31183078358552383601145163 46774617537828575401717745)
      ·
        refine ⟨35080963153371431551288309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46774617537828575401717745 35080963153371431551288309)
        ·
          refine ⟨3288840295628571707933279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35080963153371431551288309 3288840295628571707933279)
          ·
            refine ⟨4933260443442857561899919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3288840295628571707933279 4933260443442857561899919)
            ·
              refine ⟨7399890665164286342849879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4933260443442857561899919 7399890665164286342849879)
              ·
                refine ⟨11099835997746429514274819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7399890665164286342849879 11099835997746429514274819)
                ·
                  refine ⟨16649753996619644271412229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11099835997746429514274819 16649753996619644271412229)
                  ·
                    refine ⟨3121828874366183300889793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16649753996619644271412229 3121828874366183300889793)
                    ·
                      refine ⟨2341371655774637475667345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3121828874366183300889793 2341371655774637475667345)
                      ·
                        rfl

theorem cell23_4559805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_4559805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559805 prefixEnd_4559805 := by exact prefixLift 4559805
  have htrace : WordTrace (prefixWord ++ tailWord_4559805) baseStart_4559805 baseEnd_4559805 := by
    simpa [prefixWord, tailWord_4559805, baseEnd_4559805] using wordTrace_append hprefix tailTrace_4559805
  have hstable : (prefixWord ++ tailWord_4559805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559805).length < 2 ^ (prefixWord ++ tailWord_4559805).sum := by decide
  have hdescent : baseEnd_4559805 < baseStart_4559805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559807 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 6, 5]
def baseStart_4559807 : Nat := 118140960795 + 4559807 * 2 ^ 59
def prefixEnd_4559807 : Nat := 4983230072969 + 3 ^ 40 * 4559807 * 2
def baseEnd_4559807 : Nat := 780457560911982155947445

theorem tailTrace_4559807 : CollatzResearch.WordTrace tailWord_4559807 prefixEnd_4559807 780457560911982155947445 := by
  unfold tailWord_4559807
  simp only [CollatzResearch.WordTrace]
  refine ⟨166309824191605466881013675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110873216127736977920675783 166309824191605466881013675)
  ·
    refine ⟨249464736287408200321520513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166309824191605466881013675 249464736287408200321520513)
    ·
      refine ⟨187098552215556150241140385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249464736287408200321520513 187098552215556150241140385)
      ·
        refine ⟨140323914161667112680855289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187098552215556150241140385 140323914161667112680855289)
        ·
          refine ⟨105242935621250334510641467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140323914161667112680855289 105242935621250334510641467)
          ·
            refine ⟨157864403431875501765962201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105242935621250334510641467 157864403431875501765962201)
            ·
              refine ⟨118398302573906626324471651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157864403431875501765962201 118398302573906626324471651)
              ·
                refine ⟨177597453860859939486707477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118398302573906626324471651 177597453860859939486707477)
                ·
                  refine ⟨8324880649727809663439413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 177597453860859939486707477 8324880649727809663439413)
                  ·
                    refine ⟨780457560911982155947445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8324880649727809663439413 780457560911982155947445)
                    ·
                      rfl

theorem cell23_4559807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 5].length) (baseStart_4559807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559807 prefixEnd_4559807 := by exact prefixLift 4559807
  have htrace : WordTrace (prefixWord ++ tailWord_4559807) baseStart_4559807 baseEnd_4559807 := by
    simpa [prefixWord, tailWord_4559807, baseEnd_4559807] using wordTrace_append hprefix tailTrace_4559807
  have hstable : (prefixWord ++ tailWord_4559807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559807).length < 2 ^ (prefixWord ++ tailWord_4559807).sum := by decide
  have hdescent : baseEnd_4559807 < baseStart_4559807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559828 : List Nat := [2, 4, 1, 2, 1, 4, 1, 3, 5]
def baseStart_4559828 : Nat := 118140960795 + 4559828 * 2 ^ 59
def prefixEnd_4559828 : Nat := 4983230072969 + 3 ^ 40 * 4559828 * 2
def baseEnd_4559828 : Nat := 260153718425521209519971

theorem tailTrace_4559828 : CollatzResearch.WordTrace tailWord_4559828 prefixEnd_4559828 260153718425521209519971 := by
  unfold tailWord_4559828
  simp only [CollatzResearch.WordTrace]
  refine ⟨83155295062264693733764069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110873726749686258311685425 83155295062264693733764069)
  ·
    refine ⟨15591617824174630075080763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83155295062264693733764069 15591617824174630075080763)
    ·
      refine ⟨23387426736261945112621145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15591617824174630075080763 23387426736261945112621145)
      ·
        refine ⟨17540570052196458834465859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23387426736261945112621145 17540570052196458834465859)
        ·
          refine ⟨26310855078294688251698789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17540570052196458834465859 26310855078294688251698789)
          ·
            refine ⟨4933285327180254047193523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26310855078294688251698789 4933285327180254047193523)
            ·
              refine ⟨7399927990770381070790285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4933285327180254047193523 7399927990770381070790285)
              ·
                refine ⟨2774972996538892901546357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7399927990770381070790285 2774972996538892901546357)
                ·
                  refine ⟨260153718425521209519971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2774972996538892901546357 260153718425521209519971)
                  ·
                    rfl

theorem cell23_4559828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_4559828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559828 prefixEnd_4559828 := by exact prefixLift 4559828
  have htrace : WordTrace (prefixWord ++ tailWord_4559828) baseStart_4559828 baseEnd_4559828 := by
    simpa [prefixWord, tailWord_4559828, baseEnd_4559828] using wordTrace_append hprefix tailTrace_4559828
  have hstable : (prefixWord ++ tailWord_4559828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559828).length < 2 ^ (prefixWord ++ tailWord_4559828).sum := by decide
  have hdescent : baseEnd_4559828 < baseStart_4559828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559845 : List Nat := [1, 3, 1, 6, 1, 1, 3, 2, 5]
def baseStart_4559845 : Nat := 118140960795 + 4559845 * 2 ^ 59
def prefixEnd_4559845 : Nat := 4983230072969 + 3 ^ 40 * 4559845 * 2
def baseEnd_4559845 : Nat := 260154688333424146574129

theorem tailTrace_4559845 : CollatzResearch.WordTrace tailWord_4559845 prefixEnd_4559845 260154688333424146574129 := by
  unfold tailWord_4559845
  simp only [CollatzResearch.WordTrace]
  refine ⟨166311210165467799370896989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110874140110311866247264659 166311210165467799370896989)
  ·
    refine ⟨62366703812050424764086371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166311210165467799370896989 62366703812050424764086371)
    ·
      refine ⟨93550055718075637146129557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62366703812050424764086371 93550055718075637146129557)
      ·
        refine ⟨4385158861784795491224823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 93550055718075637146129557 4385158861784795491224823)
        ·
          refine ⟨6577738292677193236837235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4385158861784795491224823 6577738292677193236837235)
          ·
            refine ⟨9866607439015789855255853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6577738292677193236837235 9866607439015789855255853)
            ·
              refine ⟨3699977789630921195720945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9866607439015789855255853 3699977789630921195720945)
              ·
                refine ⟨2774983342223190896790709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3699977789630921195720945 2774983342223190896790709)
                ·
                  refine ⟨260154688333424146574129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2774983342223190896790709 260154688333424146574129)
                  ·
                    rfl

theorem cell23_4559845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 5].length) (baseStart_4559845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559845 prefixEnd_4559845 := by exact prefixLift 4559845
  have htrace : WordTrace (prefixWord ++ tailWord_4559845) baseStart_4559845 baseEnd_4559845 := by
    simpa [prefixWord, tailWord_4559845, baseEnd_4559845] using wordTrace_append hprefix tailTrace_4559845
  have hstable : (prefixWord ++ tailWord_4559845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559845).length < 2 ^ (prefixWord ++ tailWord_4559845).sum := by decide
  have hdescent : baseEnd_4559845 < baseStart_4559845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559864 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 6, 2, 3]
def baseStart_4559864 : Nat := 118140960795 + 4559864 * 2 ^ 59
def prefixEnd_4559864 : Nat := 4983230072969 + 3 ^ 40 * 4559864 * 2
def baseEnd_4559864 : Nat := 2341401951133252744829573

theorem tailTrace_4559864 : CollatzResearch.WordTrace tailWord_4559864 prefixEnd_4559864 2341401951133252744829573 := by
  unfold tailWord_4559864
  simp only [CollatzResearch.WordTrace]
  refine ⟨83155951576199482807919323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110874602101599310410559097 83155951576199482807919323)
  ·
    refine ⟨124733927364299224211878985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83155951576199482807919323 124733927364299224211878985)
    ·
      refine ⟨93550445523224418158909239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124733927364299224211878985 93550445523224418158909239)
      ·
        refine ⟨140325668284836627238363859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93550445523224418158909239 140325668284836627238363859)
        ·
          refine ⟨210488502427254940857545789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140325668284836627238363859 210488502427254940857545789)
          ·
            refine ⟨78933188410220602821579671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210488502427254940857545789 78933188410220602821579671)
            ·
              refine ⟨118399782615330904232369507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78933188410220602821579671 118399782615330904232369507)
              ·
                refine ⟨177599673922996356348554261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118399782615330904232369507 177599673922996356348554261)
                ·
                  refine ⟨8324984715140454203838481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 177599673922996356348554261 8324984715140454203838481)
                  ·
                    refine ⟨6243738536355340652878861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8324984715140454203838481 6243738536355340652878861)
                    ·
                      refine ⟨2341401951133252744829573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6243738536355340652878861 2341401951133252744829573)
                      ·
                        rfl

theorem cell23_4559864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_4559864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559864 prefixEnd_4559864 := by exact prefixLift 4559864
  have htrace : WordTrace (prefixWord ++ tailWord_4559864) baseStart_4559864 baseEnd_4559864 := by
    simpa [prefixWord, tailWord_4559864, baseEnd_4559864] using wordTrace_append hprefix tailTrace_4559864
  have hstable : (prefixWord ++ tailWord_4559864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559864).length < 2 ^ (prefixWord ++ tailWord_4559864).sum := by decide
  have hdescent : baseEnd_4559864 < baseStart_4559864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559887 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 6]
def baseStart_4559887 : Nat := 118140960795 + 4559887 * 2 ^ 59
def prefixEnd_4559887 : Nat := 4983230072969 + 3 ^ 40 * 4559887 * 2
def baseEnd_4559887 : Nat := 2341413761188306154841967

theorem tailTrace_4559887 : CollatzResearch.WordTrace tailWord_4559887 prefixEnd_4559887 2341413761188306154841967 := by
  unfold tailWord_4559887
  simp only [CollatzResearch.WordTrace]
  refine ⟨166312742031315640543925915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110875161354210427029283943 166312742031315640543925915)
  ·
    refine ⟨249469113046973460815888873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166312742031315640543925915 249469113046973460815888873)
    ·
      refine ⟨187101834785230095611916655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249469113046973460815888873 187101834785230095611916655)
      ·
        refine ⟨280652752177845143417874983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187101834785230095611916655 280652752177845143417874983)
        ·
          refine ⟨420979128266767715126812475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280652752177845143417874983 420979128266767715126812475)
          ·
            refine ⟨631468692400151572690218713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420979128266767715126812475 631468692400151572690218713)
            ·
              refine ⟨473601519300113679517664035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 631468692400151572690218713 473601519300113679517664035)
              ·
                refine ⟨710402278950170519276496053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473601519300113679517664035 710402278950170519276496053)
                ·
                  refine ⟨66600213651578486182171505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 710402278950170519276496053 66600213651578486182171505)
                  ·
                    refine ⟨49950160238683864636628629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66600213651578486182171505 49950160238683864636628629)
                    ·
                      refine ⟨2341413761188306154841967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49950160238683864636628629 2341413761188306154841967)
                      ·
                        rfl

theorem cell23_4559887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_4559887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559887 prefixEnd_4559887 := by exact prefixLift 4559887
  have htrace : WordTrace (prefixWord ++ tailWord_4559887) baseStart_4559887 baseEnd_4559887 := by
    simpa [prefixWord, tailWord_4559887, baseEnd_4559887] using wordTrace_append hprefix tailTrace_4559887
  have hstable : (prefixWord ++ tailWord_4559887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559887).length < 2 ^ (prefixWord ++ tailWord_4559887).sum := by decide
  have hdescent : baseEnd_4559887 < baseStart_4559887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559905 : List Nat := [1, 2, 3, 2, 3, 1, 4, 2, 1, 4]
def baseStart_4559905 : Nat := 118140960795 + 4559905 * 2 ^ 59
def prefixEnd_4559905 : Nat := 4983230072969 + 3 ^ 40 * 4559905 * 2
def baseEnd_4559905 : Nat := 780474334613362361472295

theorem tailTrace_4559905 : CollatzResearch.WordTrace tailWord_4559905 prefixEnd_4559905 780474334613362361472295 := by
  unfold tailWord_4559905
  simp only [CollatzResearch.WordTrace]
  refine ⟨166313398545250429618081169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110875599030166953078720779 166313398545250429618081169)
  ·
    refine ⟨124735048908937822213560877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166313398545250429618081169 124735048908937822213560877)
    ·
      refine ⟨46775643340851683330085329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124735048908937822213560877 46775643340851683330085329)
      ·
        refine ⟨35081732505638762497563997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46775643340851683330085329 35081732505638762497563997)
        ·
          refine ⟨13155649689614535936586499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35081732505638762497563997 13155649689614535936586499)
          ·
            refine ⟨19733474534421803904879749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13155649689614535936586499 19733474534421803904879749)
            ·
              refine ⟨3700026475204088232164953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19733474534421803904879749 3700026475204088232164953)
              ·
                refine ⟨2775019856403066174123715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3700026475204088232164953 2775019856403066174123715)
                ·
                  refine ⟨4162529784604599261185573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2775019856403066174123715 4162529784604599261185573)
                  ·
                    refine ⟨780474334613362361472295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4162529784604599261185573 780474334613362361472295)
                    ·
                      rfl

theorem cell23_4559905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_4559905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559905 prefixEnd_4559905 := by exact prefixLift 4559905
  have htrace : WordTrace (prefixWord ++ tailWord_4559905) baseStart_4559905 baseEnd_4559905 := by
    simpa [prefixWord, tailWord_4559905, baseEnd_4559905] using wordTrace_append hprefix tailTrace_4559905
  have hstable : (prefixWord ++ tailWord_4559905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559905).length < 2 ^ (prefixWord ++ tailWord_4559905).sum := by decide
  have hdescent : baseEnd_4559905 < baseStart_4559905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559921 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 1, 5, 2]
def baseStart_4559921 : Nat := 118140960795 + 4559921 * 2 ^ 59
def prefixEnd_4559921 : Nat := 4983230072969 + 3 ^ 40 * 4559921 * 2
def baseEnd_4559921 : Nat := 2341431219530559021816811

theorem tailTrace_4559921 : CollatzResearch.WordTrace tailWord_4559921 prefixEnd_4559921 2341431219530559021816811 := by
  unfold tailWord_4559921
  simp only [CollatzResearch.WordTrace]
  refine ⟨166313982113192464350663617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110875988075461642900442411 166313982113192464350663617)
  ·
    refine ⟨124735486584894348262997713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166313982113192464350663617 124735486584894348262997713)
    ·
      refine ⟨93551614938670761197248285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124735486584894348262997713 93551614938670761197248285)
      ·
        refine ⟨35081855602001535448968107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93551614938670761197248285 35081855602001535448968107)
        ·
          refine ⟨52622783403002303173452161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35081855602001535448968107 52622783403002303173452161)
          ·
            refine ⟨39467087552251727380089121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52622783403002303173452161 39467087552251727380089121)
            ·
              refine ⟨29600315664188795535066841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39467087552251727380089121 29600315664188795535066841)
              ·
                refine ⟨22200236748141596651300131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29600315664188795535066841 22200236748141596651300131)
                ·
                  refine ⟨33300355122212394976950197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22200236748141596651300131 33300355122212394976950197)
                  ·
                    refine ⟨3121908292707412029089081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33300355122212394976950197 3121908292707412029089081)
                    ·
                      refine ⟨2341431219530559021816811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3121908292707412029089081 2341431219530559021816811)
                      ·
                        rfl

theorem cell23_4559921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_4559921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559921 prefixEnd_4559921 := by exact prefixLift 4559921
  have htrace : WordTrace (prefixWord ++ tailWord_4559921) baseStart_4559921 baseEnd_4559921 := by
    simpa [prefixWord, tailWord_4559921, baseEnd_4559921] using wordTrace_append hprefix tailTrace_4559921
  have hstable : (prefixWord ++ tailWord_4559921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559921).length < 2 ^ (prefixWord ++ tailWord_4559921).sum := by decide
  have hdescent : baseEnd_4559921 < baseStart_4559921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559928 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 3, 1, 3]
def baseStart_4559928 : Nat := 118140960795 + 4559928 * 2 ^ 59
def prefixEnd_4559928 : Nat := 4983230072969 + 3 ^ 40 * 4559928 * 2
def baseEnd_4559928 : Nat := 2341434813895140494429279

theorem tailTrace_4559928 : CollatzResearch.WordTrace tailWord_4559928 prefixEnd_4559928 2341434813895140494429279 := by
  unfold tailWord_4559928
  simp only [CollatzResearch.WordTrace]
  refine ⟨83157118712083552273084219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110876158282778069697445625 83157118712083552273084219)
  ·
    refine ⟨124735678068125328409626329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83157118712083552273084219 124735678068125328409626329)
    ·
      refine ⟨93551758551093996307219747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124735678068125328409626329 93551758551093996307219747)
      ·
        refine ⟨140327637826640994460829621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93551758551093996307219747 140327637826640994460829621)
        ·
          refine ⟨13155716046247593230702777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140327637826640994460829621 13155716046247593230702777)
          ·
            refine ⟨9866787034685694923027083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13155716046247593230702777 9866787034685694923027083)
            ·
              refine ⟨14800180552028542384540625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9866787034685694923027083 14800180552028542384540625)
              ·
                refine ⟨11100135414021406788405469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14800180552028542384540625 11100135414021406788405469)
                ·
                  refine ⟨4162550780258027545652051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11100135414021406788405469 4162550780258027545652051)
                  ·
                    refine ⟨6243826170387041318478077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4162550780258027545652051 6243826170387041318478077)
                    ·
                      refine ⟨2341434813895140494429279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6243826170387041318478077 2341434813895140494429279)
                      ·
                        rfl

theorem cell23_4559928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 3, 1, 3].length) (baseStart_4559928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559928 prefixEnd_4559928 := by exact prefixLift 4559928
  have htrace : WordTrace (prefixWord ++ tailWord_4559928) baseStart_4559928 baseEnd_4559928 := by
    simpa [prefixWord, tailWord_4559928, baseEnd_4559928] using wordTrace_append hprefix tailTrace_4559928
  have hstable : (prefixWord ++ tailWord_4559928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559928).length < 2 ^ (prefixWord ++ tailWord_4559928).sum := by decide
  have hdescent : baseEnd_4559928 < baseStart_4559928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559944 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 1, 6]
def baseStart_4559944 : Nat := 118140960795 + 4559944 * 2 ^ 59
def prefixEnd_4559944 : Nat := 4983230072969 + 3 ^ 40 * 4559944 * 2
def baseEnd_4559944 : Nat := 780481009861870810609735

theorem tailTrace_4559944 : CollatzResearch.WordTrace tailWord_4559944 prefixEnd_4559944 780481009861870810609735 := by
  unfold tailWord_4559944
  simp only [CollatzResearch.WordTrace]
  refine ⟨83157410496054569639375443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110876547328072759519167257 83157410496054569639375443)
  ·
    refine ⟨124736115744081854459063165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83157410496054569639375443 124736115744081854459063165)
    ·
      refine ⟨46776043404030695422148687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124736115744081854459063165 46776043404030695422148687)
      ·
        refine ⟨70164065106046043133223031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46776043404030695422148687 70164065106046043133223031)
        ·
          refine ⟨105246097659069064699834547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70164065106046043133223031 105246097659069064699834547)
          ·
            refine ⟨157869146488603597049751821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105246097659069064699834547 157869146488603597049751821)
            ·
              refine ⟨59200929933226348893656933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157869146488603597049751821 59200929933226348893656933)
              ·
                refine ⟨11100174362479940417560675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59200929933226348893656933 11100174362479940417560675)
                ·
                  refine ⟨16650261543719910626341013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11100174362479940417560675 16650261543719910626341013)
                  ·
                    refine ⟨780481009861870810609735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16650261543719910626341013 780481009861870810609735)
                    ·
                      rfl

theorem cell23_4559944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_4559944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559944 prefixEnd_4559944 := by exact prefixLift 4559944
  have htrace : WordTrace (prefixWord ++ tailWord_4559944) baseStart_4559944 baseEnd_4559944 := by
    simpa [prefixWord, tailWord_4559944, baseEnd_4559944] using wordTrace_append hprefix tailTrace_4559944
  have hstable : (prefixWord ++ tailWord_4559944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559944).length < 2 ^ (prefixWord ++ tailWord_4559944).sum := by decide
  have hdescent : baseEnd_4559944 < baseStart_4559944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559961 : List Nat := [1, 2, 1, 2, 2, 1, 2, 6, 2, 4]
def baseStart_4559961 : Nat := 118140960795 + 4559961 * 2 ^ 59
def prefixEnd_4559961 : Nat := 4983230072969 + 3 ^ 40 * 4559961 * 2
def baseEnd_4559961 : Nat := 780483919585579621772209

theorem tailTrace_4559961 : CollatzResearch.WordTrace tailWord_4559961 prefixEnd_4559961 780483919585579621772209 := by
  unfold tailWord_4559961
  simp only [CollatzResearch.WordTrace]
  refine ⟨166315441033047551182119737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110876960688698367454746491 166315441033047551182119737)
  ·
    refine ⟨124736580774785663386589803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166315441033047551182119737 124736580774785663386589803)
    ·
      refine ⟨187104871162178495079884705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124736580774785663386589803 187104871162178495079884705)
      ·
        refine ⟨140328653371633871309913529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187104871162178495079884705 140328653371633871309913529)
        ·
          refine ⟨105246490028725403482435147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140328653371633871309913529 105246490028725403482435147)
          ·
            refine ⟨157869735043088105223652721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105246490028725403482435147 157869735043088105223652721)
            ·
              refine ⟨118402301282316078917739541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157869735043088105223652721 118402301282316078917739541)
              ·
                refine ⟨5550107872608566199269041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118402301282316078917739541 5550107872608566199269041)
                ·
                  refine ⟨4162580904456424649451781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5550107872608566199269041 4162580904456424649451781)
                  ·
                    refine ⟨780483919585579621772209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4162580904456424649451781 780483919585579621772209)
                    ·
                      rfl

theorem cell23_4559961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 4].length) (baseStart_4559961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559961 prefixEnd_4559961 := by exact prefixLift 4559961
  have htrace : WordTrace (prefixWord ++ tailWord_4559961) baseStart_4559961 baseEnd_4559961 := by
    simpa [prefixWord, tailWord_4559961, baseEnd_4559961] using wordTrace_append hprefix tailTrace_4559961
  have hstable : (prefixWord ++ tailWord_4559961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559961).length < 2 ^ (prefixWord ++ tailWord_4559961).sum := by decide
  have hdescent : baseEnd_4559961 < baseStart_4559961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559978 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 1, 6]
def baseStart_4559978 : Nat := 118140960795 + 4559978 * 2 ^ 59
def prefixEnd_4559978 : Nat := 4983230072969 + 3 ^ 40 * 4559978 * 2
def baseEnd_4559978 : Nat := 780486829309288432934683

theorem tailTrace_4559978 : CollatzResearch.WordTrace tailWord_4559978 prefixEnd_4559978 780486829309288432934683 := by
  unfold tailWord_4559978
  simp only [CollatzResearch.WordTrace]
  refine ⟨41579015268496490771372147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110877374049323975390325725 41579015268496490771372147)
  ·
    refine ⟨62368522902744736157058221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41579015268496490771372147 62368522902744736157058221)
    ·
      refine ⟨23388196088529276058896833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62368522902744736157058221 23388196088529276058896833)
      ·
        refine ⟨17541147066396957044172625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23388196088529276058896833 17541147066396957044172625)
        ·
          refine ⟨13155860299797717783129469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17541147066396957044172625 13155860299797717783129469)
          ·
            refine ⟨4933447612424144168673551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13155860299797717783129469 4933447612424144168673551)
            ·
              refine ⟨7400171418636216253010327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4933447612424144168673551 7400171418636216253010327)
              ·
                refine ⟨11100257127954324379515491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7400171418636216253010327 11100257127954324379515491)
                ·
                  refine ⟨16650385691931486569273237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11100257127954324379515491 16650385691931486569273237)
                  ·
                    refine ⟨780486829309288432934683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16650385691931486569273237 780486829309288432934683)
                    ·
                      rfl

theorem cell23_4559978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_4559978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559978 prefixEnd_4559978 := by exact prefixLift 4559978
  have htrace : WordTrace (prefixWord ++ tailWord_4559978) baseStart_4559978 baseEnd_4559978 := by
    simpa [prefixWord, tailWord_4559978, baseEnd_4559978] using wordTrace_append hprefix tailTrace_4559978
  have hstable : (prefixWord ++ tailWord_4559978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559978).length < 2 ^ (prefixWord ++ tailWord_4559978).sum := by decide
  have hdescent : baseEnd_4559978 < baseStart_4559978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559981 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_4559981 : Nat := 118140960795 + 4559981 * 2 ^ 59
def prefixEnd_4559981 : Nat := 4983230072969 + 3 ^ 40 * 4559981 * 2
def baseEnd_4559981 : Nat := 2341462028369828787066535

theorem tailTrace_4559981 : CollatzResearch.WordTrace tailWord_4559981 prefixEnd_4559981 2341462028369828787066535 := by
  unfold tailWord_4559981
  simp only [CollatzResearch.WordTrace]
  refine ⟨166316170492975094597847797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110877446995316729731898531 166316170492975094597847797)
  ·
    refine ⟨15592140983716415118548231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166316170492975094597847797 15592140983716415118548231)
    ·
      refine ⟨23388211475574622677822347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15592140983716415118548231 23388211475574622677822347)
      ·
        refine ⟨35082317213361934016733521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23388211475574622677822347 35082317213361934016733521)
        ·
          refine ⟨26311737910021450512550141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35082317213361934016733521 26311737910021450512550141)
          ·
            refine ⟨9866901716258043942206303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26311737910021450512550141 9866901716258043942206303)
            ·
              refine ⟨14800352574387065913309455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9866901716258043942206303 14800352574387065913309455)
              ·
                refine ⟨22200528861580598869964183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14800352574387065913309455 22200528861580598869964183)
                ·
                  refine ⟨33300793292370898304946275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22200528861580598869964183 33300793292370898304946275)
                  ·
                    refine ⟨49951189938556347457419413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33300793292370898304946275 49951189938556347457419413)
                    ·
                      refine ⟨2341462028369828787066535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49951189938556347457419413 2341462028369828787066535)
                      ·
                        rfl

theorem cell23_4559981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_4559981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559981 prefixEnd_4559981 := by exact prefixLift 4559981
  have htrace : WordTrace (prefixWord ++ tailWord_4559981) baseStart_4559981 baseEnd_4559981 := by
    simpa [prefixWord, tailWord_4559981, baseEnd_4559981] using wordTrace_append hprefix tailTrace_4559981
  have hstable : (prefixWord ++ tailWord_4559981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559981).length < 2 ^ (prefixWord ++ tailWord_4559981).sum := by decide
  have hdescent : baseEnd_4559981 < baseStart_4559981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560008 : List Nat := [2, 1, 3, 4, 3, 1, 9]
def baseStart_4560008 : Nat := 118140960795 + 4560008 * 2 ^ 59
def prefixEnd_4560008 : Nat := 4983230072969 + 3 ^ 40 * 4560008 * 2
def baseEnd_4560008 : Nat := 28907109782067903474431

theorem tailTrace_4560008 : CollatzResearch.WordTrace tailWord_4560008 prefixEnd_4560008 28907109782067903474431 := by
  unfold tailWord_4560008
  simp only [CollatzResearch.WordTrace]
  refine ⟨83158577631938639104540339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110878103509251518806053785 83158577631938639104540339)
  ·
    refine ⟨124737866447907958656810509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83158577631938639104540339 124737866447907958656810509)
    ·
      refine ⟨46776699917965484496303941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124737866447907958656810509 46776699917965484496303941)
      ·
        refine ⟨8770631234618528343056989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46776699917965484496303941 8770631234618528343056989)
        ·
          refine ⟨3288986712981948128646371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8770631234618528343056989 3288986712981948128646371)
          ·
            refine ⟨4933480069472922192969557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3288986712981948128646371 4933480069472922192969557)
            ·
              refine ⟨28907109782067903474431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4933480069472922192969557 28907109782067903474431)
              ·
                rfl

theorem cell23_4560008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 9].length) (baseStart_4560008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560008 prefixEnd_4560008 := by exact prefixLift 4560008
  have htrace : WordTrace (prefixWord ++ tailWord_4560008) baseStart_4560008 baseEnd_4560008 := by
    simpa [prefixWord, tailWord_4560008, baseEnd_4560008] using wordTrace_append hprefix tailTrace_4560008
  have hstable : (prefixWord ++ tailWord_4560008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560008).length < 2 ^ (prefixWord ++ tailWord_4560008).sum := by decide
  have hdescent : baseEnd_4560008 < baseStart_4560008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560061 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_4560061 : Nat := 118140960795 + 4560061 * 2 ^ 59
def prefixEnd_4560061 : Nat := 4983230072969 + 3 ^ 40 * 4560061 * 2
def baseEnd_4560061 : Nat := 2341503106822188474066167

theorem tailTrace_4560061 : CollatzResearch.WordTrace tailWord_4560061 prefixEnd_4560061 2341503106822188474066167 := by
  unfold tailWord_4560061
  simp only [CollatzResearch.WordTrace]
  refine ⟨166319088332685268260760037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110879392221790178840506691 166319088332685268260760037)
  ·
    refine ⟨31184829062378487798892507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166319088332685268260760037 31184829062378487798892507)
    ·
      refine ⟨46777243593567731698338761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31184829062378487798892507 46777243593567731698338761)
      ·
        refine ⟨35082932695175798773754071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46777243593567731698338761 35082932695175798773754071)
        ·
          refine ⟨52624399042763698160631107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35082932695175798773754071 52624399042763698160631107)
          ·
            refine ⟨78936598564145547240946661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52624399042763698160631107 78936598564145547240946661)
            ·
              refine ⟨14800612230777290107677499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78936598564145547240946661 14800612230777290107677499)
              ·
                refine ⟨22200918346165935161516249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14800612230777290107677499 22200918346165935161516249)
                ·
                  refine ⟨16650688759624451371137187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22200918346165935161516249 16650688759624451371137187)
                  ·
                    refine ⟨24976033139436677056705781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16650688759624451371137187 24976033139436677056705781)
                    ·
                      refine ⟨2341503106822188474066167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24976033139436677056705781 2341503106822188474066167)
                      ·
                        rfl

theorem cell23_4560061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_4560061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560061 prefixEnd_4560061 := by exact prefixLift 4560061
  have htrace : WordTrace (prefixWord ++ tailWord_4560061) baseStart_4560061 baseEnd_4560061 := by
    simpa [prefixWord, tailWord_4560061, baseEnd_4560061] using wordTrace_append hprefix tailTrace_4560061
  have hstable : (prefixWord ++ tailWord_4560061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560061).length < 2 ^ (prefixWord ++ tailWord_4560061).sum := by decide
  have hdescent : baseEnd_4560061 < baseStart_4560061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560088 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 2, 2, 4]
def baseStart_4560088 : Nat := 118140960795 + 4560088 * 2 ^ 59
def prefixEnd_4560088 : Nat := 4983230072969 + 3 ^ 40 * 4560088 * 2
def baseEnd_4560088 : Nat := 2341516970799859868428543

theorem tailTrace_4560088 : CollatzResearch.WordTrace tailWord_4560088 prefixEnd_4560088 2341516970799859868428543 := by
  unfold tailWord_4560088
  simp only [CollatzResearch.WordTrace]
  refine ⟨83160036551793725935996459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110880048735724967914661945 83160036551793725935996459)
  ·
    refine ⟨124740054827690588903994689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83160036551793725935996459 124740054827690588903994689)
    ·
      refine ⟨93555041120767941677996017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124740054827690588903994689 93555041120767941677996017)
      ·
        refine ⟨70166280840575956258497013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93555041120767941677996017 70166280840575956258497013)
        ·
          refine ⟨6578088828803995899234095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70166280840575956258497013 6578088828803995899234095)
          ·
            refine ⟨9867133243205993848851143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6578088828803995899234095 9867133243205993848851143)
            ·
              refine ⟨14800699864808990773276715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9867133243205993848851143 14800699864808990773276715)
              ·
                refine ⟨22201049797213486159915073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14800699864808990773276715 22201049797213486159915073)
                ·
                  refine ⟨16650787347910114619936305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22201049797213486159915073 16650787347910114619936305)
                  ·
                    refine ⟨12488090510932585964952229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16650787347910114619936305 12488090510932585964952229)
                    ·
                      refine ⟨2341516970799859868428543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12488090510932585964952229 2341516970799859868428543)
                      ·
                        rfl

theorem cell23_4560088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_4560088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560088 prefixEnd_4560088 := by exact prefixLift 4560088
  have htrace : WordTrace (prefixWord ++ tailWord_4560088) baseStart_4560088 baseEnd_4560088 := by
    simpa [prefixWord, tailWord_4560088, baseEnd_4560088] using wordTrace_append hprefix tailTrace_4560088
  have hstable : (prefixWord ++ tailWord_4560088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560088).length < 2 ^ (prefixWord ++ tailWord_4560088).sum := by decide
  have hdescent : baseEnd_4560088 < baseStart_4560088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560161 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_4560161 : Nat := 118140960795 + 4560161 * 2 ^ 59
def prefixEnd_4560161 : Nat := 4983230072969 + 3 ^ 40 * 4560161 * 2
def baseEnd_4560161 : Nat := 2341554454887638082815707

theorem tailTrace_4560161 : CollatzResearch.WordTrace tailWord_4560161 prefixEnd_4560161 2341554454887638082815707 := by
  unfold tailWord_4560161
  simp only [CollatzResearch.WordTrace]
  refine ⟨166322735632322985339400337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110881823754881990226266891 166322735632322985339400337)
  ·
    refine ⟨124742051724242239004550253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166322735632322985339400337 124742051724242239004550253)
    ·
      refine ⟨46778269396590839626706345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124742051724242239004550253 46778269396590839626706345)
      ·
        refine ⟨35083702047443129720029759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46778269396590839626706345 35083702047443129720029759)
        ·
          refine ⟨52625553071164694580044639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35083702047443129720029759 52625553071164694580044639)
          ·
            refine ⟨78938329606747041870066959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52625553071164694580044639 78938329606747041870066959)
            ·
              refine ⟨118407494410120562805100439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78938329606747041870066959 118407494410120562805100439)
              ·
                refine ⟨177611241615180844207650659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118407494410120562805100439 177611241615180844207650659)
                ·
                  refine ⟨266416862422771266311475989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177611241615180844207650659 266416862422771266311475989)
                  ·
                    refine ⟨12488290426067403108350437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 266416862422771266311475989 12488290426067403108350437)
                    ·
                      refine ⟨2341554454887638082815707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12488290426067403108350437 2341554454887638082815707)
                      ·
                        rfl

theorem cell23_4560161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_4560161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560161 prefixEnd_4560161 := by exact prefixLift 4560161
  have htrace : WordTrace (prefixWord ++ tailWord_4560161) baseStart_4560161 baseEnd_4560161 := by
    simpa [prefixWord, tailWord_4560161, baseEnd_4560161] using wordTrace_append hprefix tailTrace_4560161
  have hstable : (prefixWord ++ tailWord_4560161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560161).length < 2 ^ (prefixWord ++ tailWord_4560161).sum := by decide
  have hdescent : baseEnd_4560161 < baseStart_4560161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560192 : List Nat := [2, 1, 1, 2, 2, 1, 7, 2, 1, 4]
def baseStart_4560192 : Nat := 118140960795 + 4560192 * 2 ^ 59
def prefixEnd_4560192 : Nat := 4983230072969 + 3 ^ 40 * 4560192 * 2
def baseEnd_4560192 : Nat := 780523457595975820509355

theorem tailTrace_4560192 : CollatzResearch.WordTrace tailWord_4560192 prefixEnd_4560192 780523457595975820509355 := by
  unfold tailWord_4560192
  simp only [CollatzResearch.WordTrace]
  refine ⟨83161933147605338816889415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110882577530140451755852553 83161933147605338816889415)
  ·
    refine ⟨124742899721408008225334123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83161933147605338816889415 124742899721408008225334123)
    ·
      refine ⟨187114349582112012338001185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124742899721408008225334123 187114349582112012338001185)
      ·
        refine ⟨140335762186584009253500889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187114349582112012338001185 140335762186584009253500889)
        ·
          refine ⟨105251821639938006940125667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140335762186584009253500889 105251821639938006940125667)
          ·
            refine ⟨157877732459907010410188501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105251821639938006940125667 157877732459907010410188501)
            ·
              refine ⟨3700259354529070556488793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 157877732459907010410188501 3700259354529070556488793)
              ·
                refine ⟨2775194515896802917366595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3700259354529070556488793 2775194515896802917366595)
                ·
                  refine ⟨4162791773845204376049893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2775194515896802917366595 4162791773845204376049893)
                  ·
                    refine ⟨780523457595975820509355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4162791773845204376049893 780523457595975820509355)
                    ·
                      rfl

theorem cell23_4560192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 1, 4].length) (baseStart_4560192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560192 prefixEnd_4560192 := by exact prefixLift 4560192
  have htrace : WordTrace (prefixWord ++ tailWord_4560192) baseStart_4560192 baseEnd_4560192 := by
    simpa [prefixWord, tailWord_4560192, baseEnd_4560192] using wordTrace_append hprefix tailTrace_4560192
  have hstable : (prefixWord ++ tailWord_4560192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560192).length < 2 ^ (prefixWord ++ tailWord_4560192).sum := by decide
  have hdescent : baseEnd_4560192 < baseStart_4560192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560249 : List Nat := [1, 2, 1, 3, 2, 1, 6, 2, 1, 1, 3]
def baseStart_4560249 : Nat := 118140960795 + 4560249 * 2 ^ 59
def prefixEnd_4560249 : Nat := 4983230072969 + 3 ^ 40 * 4560249 * 2
def baseEnd_4560249 : Nat := 2341599641185233738515303

theorem tailTrace_4560249 : CollatzResearch.WordTrace tailWord_4560249 prefixEnd_4560249 2341599641185233738515303 := by
  unfold tailWord_4560249
  simp only [CollatzResearch.WordTrace]
  refine ⟨166325945256004176368603801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110883963504002784245735867 166325945256004176368603801)
  ·
    refine ⟨124744458942003132276452851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166325945256004176368603801 124744458942003132276452851)
    ·
      refine ⟨187116688413004698414679277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124744458942003132276452851 187116688413004698414679277)
      ·
        refine ⟨70168758154876761905504729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187116688413004698414679277 70168758154876761905504729)
        ·
          refine ⟨52626568616157571429128547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70168758154876761905504729 52626568616157571429128547)
          ·
            refine ⟨78939852924236357143692821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52626568616157571429128547 78939852924236357143692821)
            ·
              refine ⟨3700305605823579241110601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78939852924236357143692821 3700305605823579241110601)
              ·
                refine ⟨2775229204367684430832951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3700305605823579241110601 2775229204367684430832951)
                ·
                  refine ⟨4162843806551526646249427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2775229204367684430832951 4162843806551526646249427)
                  ·
                    refine ⟨6244265709827289969374141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4162843806551526646249427 6244265709827289969374141)
                    ·
                      refine ⟨2341599641185233738515303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6244265709827289969374141 2341599641185233738515303)
                      ·
                        rfl

theorem cell23_4560249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_4560249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560249 prefixEnd_4560249 := by exact prefixLift 4560249
  have htrace : WordTrace (prefixWord ++ tailWord_4560249) baseStart_4560249 baseEnd_4560249 := by
    simpa [prefixWord, tailWord_4560249, baseEnd_4560249] using wordTrace_append hprefix tailTrace_4560249
  have hstable : (prefixWord ++ tailWord_4560249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560249).length < 2 ^ (prefixWord ++ tailWord_4560249).sum := by decide
  have hdescent : baseEnd_4560249 < baseStart_4560249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560265 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 1, 6]
def baseStart_4560265 : Nat := 118140960795 + 4560265 * 2 ^ 59
def prefixEnd_4560265 : Nat := 4983230072969 + 3 ^ 40 * 4560265 * 2
def baseEnd_4560265 : Nat := 780535952291901891971743

theorem tailTrace_4560265 : CollatzResearch.WordTrace tailWord_4560265 prefixEnd_4560265 780535952291901891971743 := by
  unfold tailWord_4560265
  simp only [CollatzResearch.WordTrace]
  refine ⟨166326528823946211101186249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110884352549297474067457499 166326528823946211101186249)
  ·
    refine ⟨124744896617959658325889687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166326528823946211101186249 124744896617959658325889687)
    ·
      refine ⟨187117344926939487488834531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124744896617959658325889687 187117344926939487488834531)
      ·
        refine ⟨280676017390409231233251797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187117344926939487488834531 280676017390409231233251797)
        ·
          refine ⟨6578344157587716357029339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 280676017390409231233251797 6578344157587716357029339)
          ·
            refine ⟨9867516236381574535544009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6578344157587716357029339 9867516236381574535544009)
            ·
              refine ⟨7400637177286180901658007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9867516236381574535544009 7400637177286180901658007)
              ·
                refine ⟨11100955765929271352487011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7400637177286180901658007 11100955765929271352487011)
                ·
                  refine ⟨16651433648893907028730517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11100955765929271352487011 16651433648893907028730517)
                  ·
                    refine ⟨780535952291901891971743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16651433648893907028730517 780535952291901891971743)
                    ·
                      rfl

theorem cell23_4560265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 6].length) (baseStart_4560265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560265 prefixEnd_4560265 := by exact prefixLift 4560265
  have htrace : WordTrace (prefixWord ++ tailWord_4560265) baseStart_4560265 baseEnd_4560265 := by
    simpa [prefixWord, tailWord_4560265, baseEnd_4560265] using wordTrace_append hprefix tailTrace_4560265
  have hstable : (prefixWord ++ tailWord_4560265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560265).length < 2 ^ (prefixWord ++ tailWord_4560265).sum := by decide
  have hdescent : baseEnd_4560265 < baseStart_4560265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560285 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_4560285 : Nat := 118140960795 + 4560285 * 2 ^ 59
def prefixEnd_4560285 : Nat := 4983230072969 + 3 ^ 40 * 4560285 * 2
def baseEnd_4560285 : Nat := 2341618126488795597665137

theorem tailTrace_4560285 : CollatzResearch.WordTrace tailWord_4560285 prefixEnd_4560285 2341618126488795597665137 := by
  unfold tailWord_4560285
  simp only [CollatzResearch.WordTrace]
  refine ⟨166327258283873754516914309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110884838855915836344609539 166327258283873754516914309)
  ·
    refine ⟨31186360928226328971921433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166327258283873754516914309 31186360928226328971921433)
    ·
      refine ⟨23389770696169746728941075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31186360928226328971921433 23389770696169746728941075)
      ·
        refine ⟨35084656044254620093411613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23389770696169746728941075 35084656044254620093411613)
        ·
          refine ⟨13156746016595482535029355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35084656044254620093411613 13156746016595482535029355)
          ·
            refine ⟨19735119024893223802544033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13156746016595482535029355 19735119024893223802544033)
            ·
              refine ⟨14801339268669917851908025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19735119024893223802544033 14801339268669917851908025)
              ·
                refine ⟨11101004451502438388931019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14801339268669917851908025 11101004451502438388931019)
                ·
                  refine ⟨16651506677253657583396529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11101004451502438388931019 16651506677253657583396529)
                  ·
                    refine ⟨12488630007940243187547397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16651506677253657583396529 12488630007940243187547397)
                    ·
                      refine ⟨2341618126488795597665137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12488630007940243187547397 2341618126488795597665137)
                      ·
                        rfl

theorem cell23_4560285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_4560285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560285 prefixEnd_4560285 := by exact prefixLift 4560285
  have htrace : WordTrace (prefixWord ++ tailWord_4560285) baseStart_4560285 baseEnd_4560285 := by
    simpa [prefixWord, tailWord_4560285, baseEnd_4560285] using wordTrace_append hprefix tailTrace_4560285
  have hstable : (prefixWord ++ tailWord_4560285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560285).length < 2 ^ (prefixWord ++ tailWord_4560285).sum := by decide
  have hdescent : baseEnd_4560285 < baseStart_4560285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560286 : List Nat := [4, 3, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_4560286 : Nat := 118140960795 + 4560286 * 2 ^ 59
def prefixEnd_4560286 : Nat := 4983230072969 + 3 ^ 40 * 4560286 * 2
def baseEnd_4560286 : Nat := 780539546656483364584211

theorem tailTrace_4560286 : CollatzResearch.WordTrace tailWord_4560286 prefixEnd_4560286 780539546656483364584211 := by
  unfold tailWord_4560286
  simp only [CollatzResearch.WordTrace]
  refine ⟨20790911844608766460962589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110884863171246754458467141 20790911844608766460962589)
  ·
    refine ⟨7796591941728287422860971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20790911844608766460962589 7796591941728287422860971)
    ·
      refine ⟨11694887912592431134291457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7796591941728287422860971 11694887912592431134291457)
      ·
        refine ⟨8771165934444323350718593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11694887912592431134291457 8771165934444323350718593)
        ·
          refine ⟨6578374450833242513038945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8771165934444323350718593 6578374450833242513038945)
          ·
            refine ⟨4933780838124931884779209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6578374450833242513038945 4933780838124931884779209)
            ·
              refine ⟨3700335628593698913584407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4933780838124931884779209 3700335628593698913584407)
              ·
                refine ⟨5550503442890548370376611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3700335628593698913584407 5550503442890548370376611)
                ·
                  refine ⟨8325755164335822555564917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5550503442890548370376611 8325755164335822555564917)
                  ·
                    refine ⟨780539546656483364584211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8325755164335822555564917 780539546656483364584211)
                    ·
                      rfl

theorem cell23_4560286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_4560286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560286 prefixEnd_4560286 := by exact prefixLift 4560286
  have htrace : WordTrace (prefixWord ++ tailWord_4560286) baseStart_4560286 baseEnd_4560286 := by
    simpa [prefixWord, tailWord_4560286, baseEnd_4560286] using wordTrace_append hprefix tailTrace_4560286
  have hstable : (prefixWord ++ tailWord_4560286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560286).length < 2 ^ (prefixWord ++ tailWord_4560286).sum := by decide
  have hdescent : baseEnd_4560286 < baseStart_4560286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560340 : List Nat := [2, 4, 1, 2, 4, 1, 1, 3, 1, 2, 2]
def baseStart_4560340 : Nat := 118140960795 + 4560340 * 2 ^ 59
def prefixEnd_4560340 : Nat := 4983230072969 + 3 ^ 40 * 4560340 * 2
def baseEnd_4560340 : Nat := 2341646367924792882477385

theorem tailTrace_4560340 : CollatzResearch.WordTrace tailWord_4560340 prefixEnd_4560340 2341646367924792882477385 := by
  unfold tailWord_4560340
  simp only [CollatzResearch.WordTrace]
  refine ⟨83164632149337249455083237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110886176199116332606777649 83164632149337249455083237)
  ·
    refine ⟨15593368528000734272828107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83164632149337249455083237 15593368528000734272828107)
    ·
      refine ⟨23390052792001101409242161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15593368528000734272828107 23390052792001101409242161)
      ·
        refine ⟨17542539594000826056931621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23390052792001101409242161 17542539594000826056931621)
        ·
          refine ⟨3289226173875154885674679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17542539594000826056931621 3289226173875154885674679)
          ·
            refine ⟨4933839260812732328512019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3289226173875154885674679 4933839260812732328512019)
            ·
              refine ⟨7400758891219098492768029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4933839260812732328512019 7400758891219098492768029)
              ·
                refine ⟨2775284584207161934788011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7400758891219098492768029 2775284584207161934788011)
                ·
                  refine ⟨4162926876310742902182017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2775284584207161934788011 4162926876310742902182017)
                  ·
                    refine ⟨3122195157233057176636513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4162926876310742902182017 3122195157233057176636513)
                    ·
                      refine ⟨2341646367924792882477385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3122195157233057176636513 2341646367924792882477385)
                      ·
                        rfl

theorem cell23_4560340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_4560340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560340 prefixEnd_4560340 := by exact prefixLift 4560340
  have htrace : WordTrace (prefixWord ++ tailWord_4560340) baseStart_4560340 baseEnd_4560340 := by
    simpa [prefixWord, tailWord_4560340, baseEnd_4560340] using wordTrace_append hprefix tailTrace_4560340
  have hstable : (prefixWord ++ tailWord_4560340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560340).length < 2 ^ (prefixWord ++ tailWord_4560340).sum := by decide
  have hdescent : baseEnd_4560340 < baseStart_4560340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560349 : List Nat := [1, 4, 3, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_4560349 : Nat := 118140960795 + 4560349 * 2 ^ 59
def prefixEnd_4560349 : Nat := 4983230072969 + 3 ^ 40 * 4560349 * 2
def baseEnd_4560349 : Nat := 2341650989250683347264843

theorem tailTrace_4560349 : CollatzResearch.WordTrace tailWord_4560349 prefixEnd_4560349 2341650989250683347264843 := by
  unfold tailWord_4560349
  simp only [CollatzResearch.WordTrace]
  refine ⟨166329592555641893447244101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110886395037094595631496067 166329592555641893447244101)
  ·
    refine ⟨31186798604182855021358269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166329592555641893447244101 31186798604182855021358269)
    ·
      refine ⟨11695049476568570633009351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31186798604182855021358269 11695049476568570633009351)
      ·
        refine ⟨17542574214852855949514027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11695049476568570633009351 17542574214852855949514027)
        ·
          refine ⟨26313861322279283924271041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17542574214852855949514027 26313861322279283924271041)
          ·
            refine ⟨19735395991709462943203281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26313861322279283924271041 19735395991709462943203281)
            ·
              refine ⟨14801546993782097207402461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19735395991709462943203281 14801546993782097207402461)
              ·
                refine ⟨5550580122668286452775923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14801546993782097207402461 5550580122668286452775923)
                ·
                  refine ⟨8325870184002429679163885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5550580122668286452775923 8325870184002429679163885)
                  ·
                    refine ⟨3122201319000911129686457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8325870184002429679163885 3122201319000911129686457)
                    ·
                      refine ⟨2341650989250683347264843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3122201319000911129686457 2341650989250683347264843)
                      ·
                        rfl

theorem cell23_4560349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_4560349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560349 prefixEnd_4560349 := by exact prefixLift 4560349
  have htrace : WordTrace (prefixWord ++ tailWord_4560349) baseStart_4560349 baseEnd_4560349 := by
    simpa [prefixWord, tailWord_4560349, baseEnd_4560349] using wordTrace_append hprefix tailTrace_4560349
  have hstable : (prefixWord ++ tailWord_4560349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560349).length < 2 ^ (prefixWord ++ tailWord_4560349).sum := by decide
  have hdescent : baseEnd_4560349 < baseStart_4560349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560373 : List Nat := [1, 3, 5, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_4560373 : Nat := 118140960795 + 4560373 * 2 ^ 59
def prefixEnd_4560373 : Nat := 4983230072969 + 3 ^ 40 * 4560373 * 2
def baseEnd_4560373 : Nat := 2341663312786391253364733

theorem tailTrace_4560373 : CollatzResearch.WordTrace tailWord_4560373 prefixEnd_4560373 2341663312786391253364733 := by
  unfold tailWord_4560373
  simp only [CollatzResearch.WordTrace]
  refine ⟨166330467907554945546117773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110886978605036630364078515 166330467907554945546117773)
  ·
    refine ⟨62373925465333104579794165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166330467907554945546117773 62373925465333104579794165)
    ·
      refine ⟨5847555512374978554355703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62373925465333104579794165 5847555512374978554355703)
      ·
        refine ⟨8771333268562467831533555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5847555512374978554355703 8771333268562467831533555)
        ·
          refine ⟨13156999902843701747300333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8771333268562467831533555 13156999902843701747300333)
          ·
            refine ⟨4933874963566388155237625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13156999902843701747300333 4933874963566388155237625)
            ·
              refine ⟨3700406222674791116428219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4933874963566388155237625 3700406222674791116428219)
              ·
                refine ⟨5550609334012186674642329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3700406222674791116428219 5550609334012186674642329)
                ·
                  refine ⟨4162957000509140005981747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5550609334012186674642329 4162957000509140005981747)
                  ·
                    refine ⟨6244435500763710008972621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4162957000509140005981747 6244435500763710008972621)
                    ·
                      refine ⟨2341663312786391253364733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6244435500763710008972621 2341663312786391253364733)
                      ·
                        rfl

theorem cell23_4560373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_4560373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560373 prefixEnd_4560373 := by exact prefixLift 4560373
  have htrace : WordTrace (prefixWord ++ tailWord_4560373) baseStart_4560373 baseEnd_4560373 := by
    simpa [prefixWord, tailWord_4560373, baseEnd_4560373] using wordTrace_append hprefix tailTrace_4560373
  have hstable : (prefixWord ++ tailWord_4560373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560373).length < 2 ^ (prefixWord ++ tailWord_4560373).sum := by decide
  have hdescent : baseEnd_4560373 < baseStart_4560373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560415 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 2, 5]
def baseStart_4560415 : Nat := 118140960795 + 4560415 * 2 ^ 59
def prefixEnd_4560415 : Nat := 4983230072969 + 3 ^ 40 * 4560415 * 2
def baseEnd_4560415 : Nat := 780561626324626696346513

theorem tailTrace_4560415 : CollatzResearch.WordTrace tailWord_4560415 prefixEnd_4560415 780561626324626696346513 := by
  unfold tailWord_4560415
  simp only [CollatzResearch.WordTrace]
  refine ⟨166331999773402786719146699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110887999848935191146097799 166331999773402786719146699)
  ·
    refine ⟨249497999660104180078720049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166331999773402786719146699 249497999660104180078720049)
    ·
      refine ⟨187123499745078135059040037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249497999660104180078720049 187123499745078135059040037)
      ·
        refine ⟨35085656202202150323570007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187123499745078135059040037 35085656202202150323570007)
        ·
          refine ⟨52628484303303225485355011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35085656202202150323570007 52628484303303225485355011)
          ·
            refine ⟨78942726454954838228032517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52628484303303225485355011 78942726454954838228032517)
            ·
              refine ⟨14801761210304032167756097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78942726454954838228032517 14801761210304032167756097)
              ·
                refine ⟨11101320907728024125817073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14801761210304032167756097 11101320907728024125817073)
                ·
                  refine ⟨8325990680796018094362805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11101320907728024125817073 8325990680796018094362805)
                  ·
                    refine ⟨780561626324626696346513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8325990680796018094362805 780561626324626696346513)
                    ·
                      rfl

theorem cell23_4560415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 5].length) (baseStart_4560415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560415 prefixEnd_4560415 := by exact prefixLift 4560415
  have htrace : WordTrace (prefixWord ++ tailWord_4560415) baseStart_4560415 baseEnd_4560415 := by
    simpa [prefixWord, tailWord_4560415, baseEnd_4560415] using wordTrace_append hprefix tailTrace_4560415
  have hstable : (prefixWord ++ tailWord_4560415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560415).length < 2 ^ (prefixWord ++ tailWord_4560415).sum := by decide
  have hdescent : baseEnd_4560415 < baseStart_4560415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560428 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 4, 8]
def baseStart_4560428 : Nat := 118140960795 + 4560428 * 2 ^ 59
def prefixEnd_4560428 : Nat := 4983230072969 + 3 ^ 40 * 4560428 * 2
def baseEnd_4560428 : Nat := 780563851407462846058993

theorem tailTrace_4560428 : CollatzResearch.WordTrace tailWord_4560428 prefixEnd_4560428 780563851407462846058993 := by
  unfold tailWord_4560428
  simp only [CollatzResearch.WordTrace]
  refine ⟨83166236961177844969684969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110888315948237126626246625 83166236961177844969684969)
  ·
    refine ⟨62374677720883383727263727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83166236961177844969684969 62374677720883383727263727)
    ·
      refine ⟨93562016581325075590895591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62374677720883383727263727 93562016581325075590895591)
      ·
        refine ⟨140343024871987613386343387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93562016581325075590895591 140343024871987613386343387)
        ·
          refine ⟨210514537307981420079515081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140343024871987613386343387 210514537307981420079515081)
          ·
            refine ⟨157885902980986065059636311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210514537307981420079515081 157885902980986065059636311)
            ·
              refine ⟨236828854471479097589454467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157885902980986065059636311 236828854471479097589454467)
              ·
                refine ⟨355243281707218646384181701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236828854471479097589454467 355243281707218646384181701)
                ·
                  refine ⟨66608115320103496197034069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 355243281707218646384181701 66608115320103496197034069)
                  ·
                    refine ⟨780563851407462846058993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66608115320103496197034069 780563851407462846058993)
                    ·
                      rfl

theorem cell23_4560428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_4560428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560428 prefixEnd_4560428 := by exact prefixLift 4560428
  have htrace : WordTrace (prefixWord ++ tailWord_4560428) baseStart_4560428 baseEnd_4560428 := by
    simpa [prefixWord, tailWord_4560428, baseEnd_4560428] using wordTrace_append hprefix tailTrace_4560428
  have hstable : (prefixWord ++ tailWord_4560428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560428).length < 2 ^ (prefixWord ++ tailWord_4560428).sum := by decide
  have hdescent : baseEnd_4560428 < baseStart_4560428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560512 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 1, 5, 2]
def baseStart_4560512 : Nat := 118140960795 + 4560512 * 2 ^ 59
def prefixEnd_4560512 : Nat := 4983230072969 + 3 ^ 40 * 4560512 * 2
def baseEnd_4560512 : Nat := 2341734686597366209526593

theorem tailTrace_4560512 : CollatzResearch.WordTrace tailWord_4560512 prefixEnd_4560512 2341734686597366209526593 := by
  unfold tailWord_4560512
  simp only [CollatzResearch.WordTrace]
  refine ⟨83167768827025686142713895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110890358436034248190285193 83167768827025686142713895)
  ·
    refine ⟨124751653240538529214070843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83167768827025686142713895 124751653240538529214070843)
    ·
      refine ⟨187127479860807793821106265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124751653240538529214070843 187127479860807793821106265)
      ·
        refine ⟨140345609895605845365829699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187127479860807793821106265 140345609895605845365829699)
        ·
          refine ⟨210518414843408768048744549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140345609895605845365829699 210518414843408768048744549)
          ·
            refine ⟨39472202783139144009139603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210518414843408768048744549 39472202783139144009139603)
            ·
              refine ⟨59208304174708716013709405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39472202783139144009139603 59208304174708716013709405)
              ·
                refine ⟨22203114065515768505141027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59208304174708716013709405 22203114065515768505141027)
                ·
                  refine ⟨33304671098273652757711541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22203114065515768505141027 33304671098273652757711541)
                  ·
                    refine ⟨3122312915463154946035457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33304671098273652757711541 3122312915463154946035457)
                    ·
                      refine ⟨2341734686597366209526593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3122312915463154946035457 2341734686597366209526593)
                      ·
                        rfl

theorem cell23_4560512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 1, 5, 2].length) (baseStart_4560512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560512 prefixEnd_4560512 := by exact prefixLift 4560512
  have htrace : WordTrace (prefixWord ++ tailWord_4560512) baseStart_4560512 baseEnd_4560512 := by
    simpa [prefixWord, tailWord_4560512, baseEnd_4560512] using wordTrace_append hprefix tailTrace_4560512
  have hstable : (prefixWord ++ tailWord_4560512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560512).length < 2 ^ (prefixWord ++ tailWord_4560512).sum := by decide
  have hdescent : baseEnd_4560512 < baseStart_4560512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560536 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 3, 1, 3]
def baseStart_4560536 : Nat := 118140960795 + 4560536 * 2 ^ 59
def prefixEnd_4560536 : Nat := 4983230072969 + 3 ^ 40 * 4560536 * 2
def baseEnd_4560536 : Nat := 2341747010133074115626483

theorem tailTrace_4560536 : CollatzResearch.WordTrace tailWord_4560536 prefixEnd_4560536 2341747010133074115626483 := by
  unfold tailWord_4560536
  simp only [CollatzResearch.WordTrace]
  refine ⟨83168206502982212192150731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110890942003976282922867641 83168206502982212192150731)
  ·
    refine ⟨124752309754473318288226097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83168206502982212192150731 124752309754473318288226097)
    ·
      refine ⟨93564232315854988716169573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124752309754473318288226097 93564232315854988716169573)
      ·
        refine ⟨17543293559222810384281795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93564232315854988716169573 17543293559222810384281795)
        ·
          refine ⟨26314940338834215576422693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17543293559222810384281795 26314940338834215576422693)
          ·
            refine ⟨4934051313531415420579255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26314940338834215576422693 4934051313531415420579255)
            ·
              refine ⟨7401076970297123130868883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4934051313531415420579255 7401076970297123130868883)
              ·
                refine ⟨11101615455445684696303325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7401076970297123130868883 11101615455445684696303325)
                ·
                  refine ⟨4163105795792131761113747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11101615455445684696303325 4163105795792131761113747)
                  ·
                    refine ⟨6244658693688197641670621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4163105795792131761113747 6244658693688197641670621)
                    ·
                      refine ⟨2341747010133074115626483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6244658693688197641670621 2341747010133074115626483)
                      ·
                        rfl

theorem cell23_4560536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_4560536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560536 prefixEnd_4560536 := by exact prefixLift 4560536
  have htrace : WordTrace (prefixWord ++ tailWord_4560536) baseStart_4560536 baseEnd_4560536 := by
    simpa [prefixWord, tailWord_4560536, baseEnd_4560536] using wordTrace_append hprefix tailTrace_4560536
  have hstable : (prefixWord ++ tailWord_4560536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560536).length < 2 ^ (prefixWord ++ tailWord_4560536).sum := by decide
  have hdescent : baseEnd_4560536 < baseStart_4560536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560543 : List Nat := [1, 1, 2, 7, 2, 1, 2, 1, 6]
def baseStart_4560543 : Nat := 118140960795 + 4560543 * 2 ^ 59
def prefixEnd_4560543 : Nat := 4983230072969 + 3 ^ 40 * 4560543 * 2
def baseEnd_4560543 : Nat := 260194511610850620915439

theorem tailTrace_4560543 : CollatzResearch.WordTrace tailWord_4560543 prefixEnd_4560543 260194511610850620915439 := by
  unfold tailWord_4560543
  simp only [CollatzResearch.WordTrace]
  refine ⟨166336668316939064579806283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110891112211292709719870855 166336668316939064579806283)
  ·
    refine ⟨249505002475408596869709425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166336668316939064579806283 249505002475408596869709425)
    ·
      refine ⟨187128751856556447652282069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249505002475408596869709425 187128751856556447652282069)
      ·
        refine ⟨4385830121638041741850361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 187128751856556447652282069 4385830121638041741850361)
        ·
          refine ⟨3289372591228531306387771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4385830121638041741850361 3289372591228531306387771)
          ·
            refine ⟨4934058886842796959581657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3289372591228531306387771 4934058886842796959581657)
            ·
              refine ⟨3700544165132097719686243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4934058886842796959581657 3700544165132097719686243)
              ·
                refine ⟨5550816247698146579529365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3700544165132097719686243 5550816247698146579529365)
                ·
                  refine ⟨260194511610850620915439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5550816247698146579529365 260194511610850620915439)
                  ·
                    rfl

theorem cell23_4560543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 6].length) (baseStart_4560543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560543 prefixEnd_4560543 := by exact prefixLift 4560543
  have htrace : WordTrace (prefixWord ++ tailWord_4560543) baseStart_4560543 baseEnd_4560543 := by
    simpa [prefixWord, tailWord_4560543, baseEnd_4560543] using wordTrace_append hprefix tailTrace_4560543
  have hstable : (prefixWord ++ tailWord_4560543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560543).length < 2 ^ (prefixWord ++ tailWord_4560543).sum := by decide
  have hdescent : baseEnd_4560543 < baseStart_4560543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560559 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 5, 2, 2]
def baseStart_4560559 : Nat := 118140960795 + 4560559 * 2 ^ 59
def prefixEnd_4560559 : Nat := 4983230072969 + 3 ^ 40 * 4560559 * 2
def baseEnd_4560559 : Nat := 2341758820188127525638877

theorem tailTrace_4560559 : CollatzResearch.WordTrace tailWord_4560559 prefixEnd_4560559 2341758820188127525638877 := by
  unfold tailWord_4560559
  simp only [CollatzResearch.WordTrace]
  refine ⟨166337251884881099312388731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110891501256587399541592487 166337251884881099312388731)
  ·
    refine ⟨249505877827321648968583097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166337251884881099312388731 249505877827321648968583097)
    ·
      refine ⟨187129408370491236726437323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249505877827321648968583097 187129408370491236726437323)
      ·
        refine ⟨280694112555736855089655985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187129408370491236726437323 280694112555736855089655985)
        ·
          refine ⟨210520584416802641317241989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280694112555736855089655985 210520584416802641317241989)
          ·
            refine ⟨39472609578150495246982873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210520584416802641317241989 39472609578150495246982873)
            ·
              refine ⟨29604457183612871435237155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39472609578150495246982873 29604457183612871435237155)
              ·
                refine ⟨44406685775419307152855733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29604457183612871435237155 44406685775419307152855733)
                ·
                  refine ⟨4163126791445560045580225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44406685775419307152855733 4163126791445560045580225)
                  ·
                    refine ⟨3122345093584170034185169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4163126791445560045580225 3122345093584170034185169)
                    ·
                      refine ⟨2341758820188127525638877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3122345093584170034185169 2341758820188127525638877)
                      ·
                        rfl

theorem cell23_4560559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 2, 2].length) (baseStart_4560559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560559 prefixEnd_4560559 := by exact prefixLift 4560559
  have htrace : WordTrace (prefixWord ++ tailWord_4560559) baseStart_4560559 baseEnd_4560559 := by
    simpa [prefixWord, tailWord_4560559, baseEnd_4560559] using wordTrace_append hprefix tailTrace_4560559
  have hstable : (prefixWord ++ tailWord_4560559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560559).length < 2 ^ (prefixWord ++ tailWord_4560559).sum := by decide
  have hdescent : baseEnd_4560559 < baseStart_4560559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560572 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_4560572 : Nat := 118140960795 + 4560572 * 2 ^ 59
def prefixEnd_4560572 : Nat := 4983230072969 + 3 ^ 40 * 4560572 * 2
def baseEnd_4560572 : Nat := 2341765495436635974776317

theorem tailTrace_4560572 : CollatzResearch.WordTrace tailWord_4560572 prefixEnd_4560572 2341765495436635974776317 := by
  unfold tailWord_4560572
  simp only [CollatzResearch.WordTrace]
  refine ⟨83168863016917001266305985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110891817355889335021741313 83168863016917001266305985)
  ·
    refine ⟨62376647262687750949729489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83168863016917001266305985 62376647262687750949729489)
    ·
      refine ⟨46782485447015813212297117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62376647262687750949729489 46782485447015813212297117)
      ·
        refine ⟨17543432042630929954611419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46782485447015813212297117 17543432042630929954611419)
        ·
          refine ⟨26315148063946394931917129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17543432042630929954611419 26315148063946394931917129)
          ·
            refine ⟨19736361047959796198937847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26315148063946394931917129 19736361047959796198937847)
            ·
              refine ⟨29604541571939694298406771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19736361047959796198937847 29604541571939694298406771)
              ·
                refine ⟨44406812357909541447610157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29604541571939694298406771 44406812357909541447610157)
                ·
                  refine ⟨16652554634216078042853809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44406812357909541447610157 16652554634216078042853809)
                  ·
                    refine ⟨12489415975662058532140357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16652554634216078042853809 12489415975662058532140357)
                    ·
                      refine ⟨2341765495436635974776317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12489415975662058532140357 2341765495436635974776317)
                      ·
                        rfl

theorem cell23_4560572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_4560572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560572 prefixEnd_4560572 := by exact prefixLift 4560572
  have htrace : WordTrace (prefixWord ++ tailWord_4560572) baseStart_4560572 baseEnd_4560572 := by
    simpa [prefixWord, tailWord_4560572, baseEnd_4560572] using wordTrace_append hprefix tailTrace_4560572
  have hstable : (prefixWord ++ tailWord_4560572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560572).length < 2 ^ (prefixWord ++ tailWord_4560572).sum := by decide
  have hdescent : baseEnd_4560572 < baseStart_4560572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560586 : List Nat := [3, 1, 2, 1, 5, 1, 2, 2, 2, 4]
def baseStart_4560586 : Nat := 118140960795 + 4560586 * 2 ^ 59
def prefixEnd_4560586 : Nat := 4983230072969 + 3 ^ 40 * 4560586 * 2
def baseEnd_4560586 : Nat := 780590894721932973333751

theorem tailTrace_4560586 : CollatzResearch.WordTrace tailWord_4560586 prefixEnd_4560586 780590894721932973333751 := by
  unfold tailWord_4560586
  simp only [CollatzResearch.WordTrace]
  refine ⟨41584559163945820730905403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110892157770522188615747741 41584559163945820730905403)
  ·
    refine ⟨62376838745918731096358105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41584559163945820730905403 62376838745918731096358105)
    ·
      refine ⟨46782629059439048322268579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62376838745918731096358105 46782629059439048322268579)
      ·
        refine ⟨70173943589158572483402869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46782629059439048322268579 70173943589158572483402869)
        ·
          refine ⟨6578807211483616170319019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70173943589158572483402869 6578807211483616170319019)
          ·
            refine ⟨9868210817225424255478529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6578807211483616170319019 9868210817225424255478529)
            ·
              refine ⟨7401158112919068191608897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9868210817225424255478529 7401158112919068191608897)
              ·
                refine ⟨5550868584689301143706673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7401158112919068191608897 5550868584689301143706673)
                ·
                  refine ⟨4163151438516975857780005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5550868584689301143706673 4163151438516975857780005)
                  ·
                    refine ⟨780590894721932973333751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4163151438516975857780005 780590894721932973333751)
                    ·
                      rfl

theorem cell23_4560586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_4560586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560586 prefixEnd_4560586 := by exact prefixLift 4560586
  have htrace : WordTrace (prefixWord ++ tailWord_4560586) baseStart_4560586 baseEnd_4560586 := by
    simpa [prefixWord, tailWord_4560586, baseEnd_4560586] using wordTrace_append hprefix tailTrace_4560586
  have hstable : (prefixWord ++ tailWord_4560586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560586).length < 2 ^ (prefixWord ++ tailWord_4560586).sum := by decide
  have hdescent : baseEnd_4560586 < baseStart_4560586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560593 : List Nat := [1, 2, 2, 1, 2, 5, 1, 4, 1, 2, 2]
def baseStart_4560593 : Nat := 118140960795 + 4560593 * 2 ^ 59
def prefixEnd_4560593 : Nat := 4983230072969 + 3 ^ 40 * 4560593 * 2
def baseEnd_4560593 : Nat := 2341776278530380392613721

theorem tailTrace_4560593 : CollatzResearch.WordTrace tailWord_4560593 prefixEnd_4560593 2341776278530380392613721 := by
  unfold tailWord_4560593
  simp only [CollatzResearch.WordTrace]
  refine ⟨166338491966757923119126433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110892327977838615412750955 166338491966757923119126433)
  ·
    refine ⟨124753868975068442339344825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166338491966757923119126433 124753868975068442339344825)
    ·
      refine ⟨93565401731301331754508619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124753868975068442339344825 93565401731301331754508619)
      ·
        refine ⟨140348102596951997631762929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93565401731301331754508619 140348102596951997631762929)
        ·
          refine ⟨105261076947713998223822197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140348102596951997631762929 105261076947713998223822197)
          ·
            refine ⟨9868225963848187333483331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105261076947713998223822197 9868225963848187333483331)
            ·
              refine ⟨14802338945772281000224997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9868225963848187333483331 14802338945772281000224997)
              ·
                refine ⟨2775438552332302687542187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14802338945772281000224997 2775438552332302687542187)
                ·
                  refine ⟨4163157828498454031313281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2775438552332302687542187 4163157828498454031313281)
                  ·
                    refine ⟨3122368371373840523484961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4163157828498454031313281 3122368371373840523484961)
                    ·
                      refine ⟨2341776278530380392613721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3122368371373840523484961 2341776278530380392613721)
                      ·
                        rfl

theorem cell23_4560593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 1, 2, 2].length) (baseStart_4560593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560593 prefixEnd_4560593 := by exact prefixLift 4560593
  have htrace : WordTrace (prefixWord ++ tailWord_4560593) baseStart_4560593 baseEnd_4560593 := by
    simpa [prefixWord, tailWord_4560593, baseEnd_4560593] using wordTrace_append hprefix tailTrace_4560593
  have hstable : (prefixWord ++ tailWord_4560593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560593).length < 2 ^ (prefixWord ++ tailWord_4560593).sum := by decide
  have hdescent : baseEnd_4560593 < baseStart_4560593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560619 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 3, 3, 2]
def baseStart_4560619 : Nat := 118140960795 + 4560619 * 2 ^ 59
def prefixEnd_4560619 : Nat := 4983230072969 + 3 ^ 40 * 4560619 * 2
def baseEnd_4560619 : Nat := 2341789629027397290888601

theorem tailTrace_4560619 : CollatzResearch.WordTrace tailWord_4560619 prefixEnd_4560619 2341789629027397290888601 := by
  unfold tailWord_4560619
  simp only [CollatzResearch.WordTrace]
  refine ⟨166339440264663729559572911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110892960176442486373048607 166339440264663729559572911)
  ·
    refine ⟨249509160396995594339359367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166339440264663729559572911 249509160396995594339359367)
    ·
      refine ⟨374263740595493391509039051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249509160396995594339359367 374263740595493391509039051)
      ·
        refine ⟨561395610893240087263558577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374263740595493391509039051 561395610893240087263558577)
        ·
          refine ⟨421046708169930065447668933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 561395610893240087263558577 421046708169930065447668933)
          ·
            refine ⟨78946257781861887271437925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 421046708169930065447668933 78946257781861887271437925)
            ·
              refine ⟨14802423334099103863394611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78946257781861887271437925 14802423334099103863394611)
              ·
                refine ⟨22203635001148655795091917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14802423334099103863394611 22203635001148655795091917)
                ·
                  refine ⟨8326363125430745923159469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22203635001148655795091917 8326363125430745923159469)
                  ·
                    refine ⟨3122386172036529721184801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8326363125430745923159469 3122386172036529721184801)
                    ·
                      refine ⟨2341789629027397290888601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3122386172036529721184801 2341789629027397290888601)
                      ·
                        rfl

theorem cell23_4560619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 3, 2].length) (baseStart_4560619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560619 prefixEnd_4560619 := by exact prefixLift 4560619
  have htrace : WordTrace (prefixWord ++ tailWord_4560619) baseStart_4560619 baseEnd_4560619 := by
    simpa [prefixWord, tailWord_4560619, baseEnd_4560619] using wordTrace_append hprefix tailTrace_4560619
  have hstable : (prefixWord ++ tailWord_4560619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560619).length < 2 ^ (prefixWord ++ tailWord_4560619).sum := by decide
  have hdescent : baseEnd_4560619 < baseStart_4560619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560622 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_4560622 : Nat := 118140960795 + 4560622 * 2 ^ 59
def prefixEnd_4560622 : Nat := 4983230072969 + 3 ^ 40 * 4560622 * 2
def baseEnd_4560622 : Nat := 2341791169469360779151087

theorem tailTrace_4560622 : CollatzResearch.WordTrace tailWord_4560622 prefixEnd_4560622 2341791169469360779151087 := by
  unfold tailWord_4560622
  simp only [CollatzResearch.WordTrace]
  refine ⟨20792443710456607633991515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110893033122435240714621413 20792443710456607633991515)
  ·
    refine ⟨31188665565684911450987273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20792443710456607633991515 31188665565684911450987273)
    ·
      refine ⟨23391499174263683588240455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31188665565684911450987273 23391499174263683588240455)
      ·
        refine ⟨35087248761395525382360683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23391499174263683588240455 35087248761395525382360683)
        ·
          refine ⟨52630873142093288073541025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35087248761395525382360683 52630873142093288073541025)
          ·
            refine ⟨39473154856569966055155769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52630873142093288073541025 39473154856569966055155769)
            ·
              refine ⟨29604866142427474541366827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39473154856569966055155769 29604866142427474541366827)
              ·
                refine ⟨44407299213641211812050241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29604866142427474541366827 44407299213641211812050241)
                ·
                  refine ⟨33305474410230908859037681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44407299213641211812050241 33305474410230908859037681)
                  ·
                    refine ⟨24979105807673181644278261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33305474410230908859037681 24979105807673181644278261)
                    ·
                      refine ⟨2341791169469360779151087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24979105807673181644278261 2341791169469360779151087)
                      ·
                        rfl

theorem cell23_4560622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_4560622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560622 prefixEnd_4560622 := by exact prefixLift 4560622
  have htrace : WordTrace (prefixWord ++ tailWord_4560622) baseStart_4560622 baseEnd_4560622 := by
    simpa [prefixWord, tailWord_4560622, baseEnd_4560622] using wordTrace_append hprefix tailTrace_4560622
  have hstable : (prefixWord ++ tailWord_4560622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560622).length < 2 ^ (prefixWord ++ tailWord_4560622).sum := by decide
  have hdescent : baseEnd_4560622 < baseStart_4560622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560636 : List Nat := [2, 2, 2, 1, 3, 1, 3, 3, 1, 3, 2]
def baseStart_4560636 : Nat := 118140960795 + 4560636 * 2 ^ 59
def prefixEnd_4560636 : Nat := 4983230072969 + 3 ^ 40 * 4560636 * 2
def baseEnd_4560636 : Nat := 2341798358198523724376023

theorem tailTrace_4560636 : CollatzResearch.WordTrace tailWord_4560636 prefixEnd_4560636 2341798358198523724376023 := by
  unfold tailWord_4560636
  simp only [CollatzResearch.WordTrace]
  refine ⟨83170030152801070731470881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110893373537068094308627841 83170030152801070731470881)
  ·
    refine ⟨62377522614600803048603161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83170030152801070731470881 62377522614600803048603161)
    ·
      refine ⟨46783141960950602286452371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62377522614600803048603161 46783141960950602286452371)
      ·
        refine ⟨70174712941425903429678557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46783141960950602286452371 70174712941425903429678557)
        ·
          refine ⟨26315517353034713786129459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70174712941425903429678557 26315517353034713786129459)
          ·
            refine ⟨39473276029552070679194189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26315517353034713786129459 39473276029552070679194189)
            ·
              refine ⟨14802478511082026504697821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39473276029552070679194189 14802478511082026504697821)
              ·
                refine ⟨5550929441655759939261683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14802478511082026504697821 5550929441655759939261683)
                ·
                  refine ⟨8326394162483639908892525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5550929441655759939261683 8326394162483639908892525)
                  ·
                    refine ⟨3122397810931364965834697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8326394162483639908892525 3122397810931364965834697)
                    ·
                      refine ⟨2341798358198523724376023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3122397810931364965834697 2341798358198523724376023)
                      ·
                        rfl

theorem cell23_4560636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_4560636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560636 prefixEnd_4560636 := by exact prefixLift 4560636
  have htrace : WordTrace (prefixWord ++ tailWord_4560636) baseStart_4560636 baseEnd_4560636 := by
    simpa [prefixWord, tailWord_4560636, baseEnd_4560636] using wordTrace_append hprefix tailTrace_4560636
  have hstable : (prefixWord ++ tailWord_4560636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560636).length < 2 ^ (prefixWord ++ tailWord_4560636).sum := by decide
  have hdescent : baseEnd_4560636 < baseStart_4560636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560652 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 1, 6, 3]
def baseStart_4560652 : Nat := 118140960795 + 4560652 * 2 ^ 59
def prefixEnd_4560652 : Nat := 4983230072969 + 3 ^ 40 * 4560652 * 2
def baseEnd_4560652 : Nat := 2341806573888995661775949

theorem tailTrace_4560652 : CollatzResearch.WordTrace tailWord_4560652 prefixEnd_4560652 2341806573888995661775949 := by
  unfold tailWord_4560652
  simp only [CollatzResearch.WordTrace]
  refine ⟨83170321936772088097762105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110893762582362784130349473 83170321936772088097762105)
  ·
    refine ⟨62377741452579066073321579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83170321936772088097762105 62377741452579066073321579)
    ·
      refine ⟨93566612178868599109982369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62377741452579066073321579 93566612178868599109982369)
      ·
        refine ⟨70174959134151449332486777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93566612178868599109982369 70174959134151449332486777)
        ·
          refine ⟨52631219350613586999365083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70174959134151449332486777 52631219350613586999365083)
          ·
            refine ⟨78946829025920380499047625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52631219350613586999365083 78946829025920380499047625)
            ·
              refine ⟨59210121769440285374285719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78946829025920380499047625 59210121769440285374285719)
              ·
                refine ⟨88815182654160428061428579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59210121769440285374285719 88815182654160428061428579)
                ·
                  refine ⟨133222773981240642092142869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88815182654160428061428579 133222773981240642092142869)
                  ·
                    refine ⟨6244817530370655098069197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 133222773981240642092142869 6244817530370655098069197)
                    ·
                      refine ⟨2341806573888995661775949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6244817530370655098069197 2341806573888995661775949)
                      ·
                        rfl

theorem cell23_4560652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_4560652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560652 prefixEnd_4560652 := by exact prefixLift 4560652
  have htrace : WordTrace (prefixWord ++ tailWord_4560652) baseStart_4560652 baseEnd_4560652 := by
    simpa [prefixWord, tailWord_4560652, baseEnd_4560652] using wordTrace_append hprefix tailTrace_4560652
  have hstable : (prefixWord ++ tailWord_4560652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560652).length < 2 ^ (prefixWord ++ tailWord_4560652).sum := by decide
  have hdescent : baseEnd_4560652 < baseStart_4560652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560666 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2]
def baseStart_4560666 : Nat := 118140960795 + 4560666 * 2 ^ 59
def prefixEnd_4560666 : Nat := 4983230072969 + 3 ^ 40 * 4560666 * 2
def baseEnd_4560666 : Nat := 2341813762618158607000885

theorem tailTrace_4560666 : CollatzResearch.WordTrace tailWord_4560666 prefixEnd_4560666 2341813762618158607000885 := by
  unfold tailWord_4560666
  simp only [CollatzResearch.WordTrace]
  refine ⟨41585288623873364146633463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110894102996995637724355901 41585288623873364146633463)
  ·
    refine ⟨62377932935810046219950195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41585288623873364146633463 62377932935810046219950195)
    ·
      refine ⟨93566899403715069329925293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62377932935810046219950195 93566899403715069329925293)
      ·
        refine ⟨35087587276393150998721985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93566899403715069329925293 35087587276393150998721985)
        ·
          refine ⟨26315690457294863249041489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35087587276393150998721985 26315690457294863249041489)
          ·
            refine ⟨19736767842971147436781117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26315690457294863249041489 19736767842971147436781117)
            ·
              refine ⟨7401287941114180288792919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19736767842971147436781117 7401287941114180288792919)
              ·
                refine ⟨11101931911671270433189379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7401287941114180288792919 11101931911671270433189379)
                ·
                  refine ⟨16652897867506905649784069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11101931911671270433189379 16652897867506905649784069)
                  ·
                    refine ⟨3122418350157544809334513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16652897867506905649784069 3122418350157544809334513)
                    ·
                      refine ⟨2341813762618158607000885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3122418350157544809334513 2341813762618158607000885)
                      ·
                        rfl

theorem cell23_4560666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_4560666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560666 prefixEnd_4560666 := by exact prefixLift 4560666
  have htrace : WordTrace (prefixWord ++ tailWord_4560666) baseStart_4560666 baseEnd_4560666 := by
    simpa [prefixWord, tailWord_4560666, baseEnd_4560666] using wordTrace_append hprefix tailTrace_4560666
  have hstable : (prefixWord ++ tailWord_4560666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560666).length < 2 ^ (prefixWord ++ tailWord_4560666).sum := by decide
  have hdescent : baseEnd_4560666 < baseStart_4560666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560672 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 7]
def baseStart_4560672 : Nat := 118140960795 + 4560672 * 2 ^ 59
def prefixEnd_4560672 : Nat := 4983230072969 + 3 ^ 40 * 4560672 * 2
def baseEnd_4560672 : Nat := 260201871500231731502873

theorem tailTrace_4560672 : CollatzResearch.WordTrace tailWord_4560672 prefixEnd_4560672 260201871500231731502873 := by
  unfold tailWord_4560672
  simp only [CollatzResearch.WordTrace]
  refine ⟨83170686666735859805626135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110894248888981146407501513 83170686666735859805626135)
  ·
    refine ⟨124756030000103789708439203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83170686666735859805626135 124756030000103789708439203)
    ·
      refine ⟨187134045000155684562658805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124756030000103789708439203 187134045000155684562658805)
      ·
        refine ⟨17543816718764595427749263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 187134045000155684562658805 17543816718764595427749263)
        ·
          refine ⟨26315725078146893141623895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17543816718764595427749263 26315725078146893141623895)
          ·
            refine ⟨39473587617220339712435843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26315725078146893141623895 39473587617220339712435843)
            ·
              refine ⟨59210381425830509568653765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39473587617220339712435843 59210381425830509568653765)
              ·
                refine ⟨11101946517343220544122581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59210381425830509568653765 11101946517343220544122581)
                ·
                  refine ⟨260201871500231731502873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11101946517343220544122581 260201871500231731502873)
                  ·
                    rfl

theorem cell23_4560672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 7].length) (baseStart_4560672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560672 prefixEnd_4560672 := by exact prefixLift 4560672
  have htrace : WordTrace (prefixWord ++ tailWord_4560672) baseStart_4560672 baseEnd_4560672 := by
    simpa [prefixWord, tailWord_4560672, baseEnd_4560672] using wordTrace_append hprefix tailTrace_4560672
  have hstable : (prefixWord ++ tailWord_4560672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560672).length < 2 ^ (prefixWord ++ tailWord_4560672).sum := by decide
  have hdescent : baseEnd_4560672 < baseStart_4560672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560686 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_4560686 : Nat := 118140960795 + 4560686 * 2 ^ 59
def prefixEnd_4560686 : Nat := 4983230072969 + 3 ^ 40 * 4560686 * 2
def baseEnd_4560686 : Nat := 2341824032231248528750793

theorem tailTrace_4560686 : CollatzResearch.WordTrace tailWord_4560686 prefixEnd_4560686 2341824032231248528750793 := by
  unfold tailWord_4560686
  simp only [CollatzResearch.WordTrace]
  refine ⟨20792735494427625000282739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110894589303614000001507941 20792735494427625000282739)
  ·
    refine ⟨31189103241641437500424109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20792735494427625000282739 31189103241641437500424109)
    ·
      refine ⟨11695913715615539062659041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31189103241641437500424109 11695913715615539062659041)
      ·
        refine ⟨8771935286711654296994281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11695913715615539062659041 8771935286711654296994281)
        ·
          refine ⟨6578951465033740722745711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8771935286711654296994281 6578951465033740722745711)
          ·
            refine ⟨9868427197550611084118567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6578951465033740722745711 9868427197550611084118567)
            ·
              refine ⟨14802640796325916626177851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9868427197550611084118567 14802640796325916626177851)
              ·
                refine ⟨22203961194488874939266777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14802640796325916626177851 22203961194488874939266777)
                ·
                  refine ⟨16652970895866656204450083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22203961194488874939266777 16652970895866656204450083)
                  ·
                    refine ⟨24979456343799984306675125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16652970895866656204450083 24979456343799984306675125)
                    ·
                      refine ⟨2341824032231248528750793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24979456343799984306675125 2341824032231248528750793)
                      ·
                        rfl

theorem cell23_4560686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_4560686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560686 prefixEnd_4560686 := by exact prefixLift 4560686
  have htrace : WordTrace (prefixWord ++ tailWord_4560686) baseStart_4560686 baseEnd_4560686 := by
    simpa [prefixWord, tailWord_4560686, baseEnd_4560686] using wordTrace_append hprefix tailTrace_4560686
  have hstable : (prefixWord ++ tailWord_4560686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560686).length < 2 ^ (prefixWord ++ tailWord_4560686).sum := by decide
  have hdescent : baseEnd_4560686 < baseStart_4560686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560709 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 2, 5, 2]
def baseStart_4560709 : Nat := 118140960795 + 4560709 * 2 ^ 59
def prefixEnd_4560709 : Nat := 4983230072969 + 3 ^ 40 * 4560709 * 2
def baseEnd_4560709 : Nat := 2341835842286301938763187

theorem tailTrace_4560709 : CollatzResearch.WordTrace tailWord_4560709 prefixEnd_4560709 2341835842286301938763187 := by
  unfold tailWord_4560709
  simp only [CollatzResearch.WordTrace]
  refine ⟨166342722834337674930349181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110895148556225116620232787 166342722834337674930349181)
  ·
    refine ⟨62378521062876628098880943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166342722834337674930349181 62378521062876628098880943)
    ·
      refine ⟨93567781594314942148321415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62378521062876628098880943 93567781594314942148321415)
      ·
        refine ⟨140351672391472413222482123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93567781594314942148321415 140351672391472413222482123)
        ·
          refine ⟨210527508587208619833723185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140351672391472413222482123 210527508587208619833723185)
          ·
            refine ⟨157895631440406464875292389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210527508587208619833723185 157895631440406464875292389)
            ·
              refine ⟨29605430895076212164117323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157895631440406464875292389 29605430895076212164117323)
              ·
                refine ⟨44408146342614318246175985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29605430895076212164117323 44408146342614318246175985)
                ·
                  refine ⟨33306109756960738684631989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44408146342614318246175985 33306109756960738684631989)
                  ·
                    refine ⟨3122447789715069251684249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33306109756960738684631989 3122447789715069251684249)
                    ·
                      refine ⟨2341835842286301938763187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3122447789715069251684249 2341835842286301938763187)
                      ·
                        rfl

theorem cell23_4560709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 5, 2].length) (baseStart_4560709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560709 prefixEnd_4560709 := by exact prefixLift 4560709
  have htrace : WordTrace (prefixWord ++ tailWord_4560709) baseStart_4560709 baseEnd_4560709 := by
    simpa [prefixWord, tailWord_4560709, baseEnd_4560709] using wordTrace_append hprefix tailTrace_4560709
  have hstable : (prefixWord ++ tailWord_4560709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560709).length < 2 ^ (prefixWord ++ tailWord_4560709).sum := by decide
  have hdescent : baseEnd_4560709 < baseStart_4560709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560712 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_4560712 : Nat := 118140960795 + 4560712 * 2 ^ 59
def prefixEnd_4560712 : Nat := 4983230072969 + 3 ^ 40 * 4560712 * 2
def baseEnd_4560712 : Nat := 2341837382728265427025673

theorem tailTrace_4560712 : CollatzResearch.WordTrace tailWord_4560712 prefixEnd_4560712 2341837382728265427025673 := by
  unfold tailWord_4560712
  simp only [CollatzResearch.WordTrace]
  refine ⟨83171416126663403221354195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110895221502217870961805593 83171416126663403221354195)
  ·
    refine ⟨124757124189995104832031293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83171416126663403221354195 124757124189995104832031293)
    ·
      refine ⟨46783921571248164312011735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124757124189995104832031293 46783921571248164312011735)
      ·
        refine ⟨70175882356872246468017603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46783921571248164312011735 70175882356872246468017603)
        ·
          refine ⟨105263823535308369702026405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70175882356872246468017603 105263823535308369702026405)
          ·
            refine ⟨19736966912870319319129951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105263823535308369702026405 19736966912870319319129951)
            ·
              refine ⟨29605450369305478978694927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19736966912870319319129951 29605450369305478978694927)
              ·
                refine ⟨44408175553958218468042391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29605450369305478978694927 44408175553958218468042391)
                ·
                  refine ⟨66612263330937327702063587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44408175553958218468042391 66612263330937327702063587)
                  ·
                    refine ⟨99918394996405991553095381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66612263330937327702063587 99918394996405991553095381)
                    ·
                      refine ⟨2341837382728265427025673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99918394996405991553095381 2341837382728265427025673)
                      ·
                        rfl

theorem cell23_4560712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_4560712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560712 prefixEnd_4560712 := by exact prefixLift 4560712
  have htrace : WordTrace (prefixWord ++ tailWord_4560712) baseStart_4560712 baseEnd_4560712 := by
    simpa [prefixWord, tailWord_4560712, baseEnd_4560712] using wordTrace_append hprefix tailTrace_4560712
  have hstable : (prefixWord ++ tailWord_4560712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560712).length < 2 ^ (prefixWord ++ tailWord_4560712).sum := by decide
  have hdescent : baseEnd_4560712 < baseStart_4560712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560717 : List Nat := [1, 6, 1, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_4560717 : Nat := 118140960795 + 4560717 * 2 ^ 59
def prefixEnd_4560717 : Nat := 4983230072969 + 3 ^ 40 * 4560717 * 2
def baseEnd_4560717 : Nat := 2341839950131537907463151

theorem tailTrace_4560717 : CollatzResearch.WordTrace tailWord_4560717 prefixEnd_4560717 2341839950131537907463151 := by
  unfold tailWord_4560717
  simp only [CollatzResearch.WordTrace]
  refine ⟨166343014618308692296640405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110895343078872461531093603 166343014618308692296640405)
  ·
    refine ⟨7797328810233219951405019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 166343014618308692296640405 7797328810233219951405019)
    ·
      refine ⟨11695993215349829927107529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7797328810233219951405019 11695993215349829927107529)
      ·
        refine ⟨8771994911512372445330647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11695993215349829927107529 8771994911512372445330647)
        ·
          refine ⟨13157992367268558667995971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8771994911512372445330647 13157992367268558667995971)
          ·
            refine ⟨19736988550902838001993957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13157992367268558667995971 19736988550902838001993957)
            ·
              refine ⟨3700685353294282125373867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19736988550902838001993957 3700685353294282125373867)
              ·
                refine ⟨5551028029941423188060801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3700685353294282125373867 5551028029941423188060801)
                ·
                  refine ⟨4163271022456067391045601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5551028029941423188060801 4163271022456067391045601)
                  ·
                    refine ⟨3122453266842050543284201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4163271022456067391045601 3122453266842050543284201)
                    ·
                      refine ⟨2341839950131537907463151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3122453266842050543284201 2341839950131537907463151)
                      ·
                        rfl

theorem cell23_4560717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_4560717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560717 prefixEnd_4560717 := by exact prefixLift 4560717
  have htrace : WordTrace (prefixWord ++ tailWord_4560717) baseStart_4560717 baseEnd_4560717 := by
    simpa [prefixWord, tailWord_4560717, baseEnd_4560717] using wordTrace_append hprefix tailTrace_4560717
  have hstable : (prefixWord ++ tailWord_4560717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560717).length < 2 ^ (prefixWord ++ tailWord_4560717).sum := by decide
  have hdescent : baseEnd_4560717 < baseStart_4560717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560752 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 6]
def baseStart_4560752 : Nat := 118140960795 + 4560752 * 2 ^ 59
def prefixEnd_4560752 : Nat := 4983230072969 + 3 ^ 40 * 4560752 * 2
def baseEnd_4560752 : Nat := 2341857921954445270525489

theorem tailTrace_4560752 : CollatzResearch.WordTrace tailWord_4560752 prefixEnd_4560752 2341857921954445270525489 := by
  unfold tailWord_4560752
  simp only [CollatzResearch.WordTrace]
  refine ⟨83172145586590946637082255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110896194115454595516109673 83172145586590946637082255)
  ·
    refine ⟨124758218379886419955623383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83172145586590946637082255 124758218379886419955623383)
    ·
      refine ⟨187137327569829629933435075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124758218379886419955623383 187137327569829629933435075)
      ·
        refine ⟨280705991354744444900152613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187137327569829629933435075 280705991354744444900152613)
        ·
          refine ⟨52632373379014583418778615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 280705991354744444900152613 52632373379014583418778615)
          ·
            refine ⟨78948560068521875128167923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52632373379014583418778615 78948560068521875128167923)
            ·
              refine ⟨118422840102782812692251885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78948560068521875128167923 118422840102782812692251885)
              ·
                refine ⟨44408565038543554759594457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118422840102782812692251885 44408565038543554759594457)
                ·
                  refine ⟨33306423778907666069695843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44408565038543554759594457 33306423778907666069695843)
                  ·
                    refine ⟨49959635668361499104543765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33306423778907666069695843 49959635668361499104543765)
                    ·
                      refine ⟨2341857921954445270525489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49959635668361499104543765 2341857921954445270525489)
                      ·
                        rfl

theorem cell23_4560752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_4560752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560752 prefixEnd_4560752 := by exact prefixLift 4560752
  have htrace : WordTrace (prefixWord ++ tailWord_4560752) baseStart_4560752 baseEnd_4560752 := by
    simpa [prefixWord, tailWord_4560752, baseEnd_4560752] using wordTrace_append hprefix tailTrace_4560752
  have hstable : (prefixWord ++ tailWord_4560752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560752).length < 2 ^ (prefixWord ++ tailWord_4560752).sum := by decide
  have hdescent : baseEnd_4560752 < baseStart_4560752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560762 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 8]
def baseStart_4560762 : Nat := 118140960795 + 4560762 * 2 ^ 59
def prefixEnd_4560762 : Nat := 4983230072969 + 3 ^ 40 * 4560762 * 2
def baseEnd_4560762 : Nat := 260207006306776692377827

theorem tailTrace_4560762 : CollatzResearch.WordTrace tailWord_4560762 prefixEnd_4560762 260207006306776692377827 := by
  unfold tailWord_4560762
  simp only [CollatzResearch.WordTrace]
  refine ⟨41586163975786416245507135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110896437268763776654685693 41586163975786416245507135)
  ·
    refine ⟨62379245963679624368260703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41586163975786416245507135 62379245963679624368260703)
    ·
      refine ⟨93568868945519436552391055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62379245963679624368260703 93568868945519436552391055)
      ·
        refine ⟨140353303418279154828586583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93568868945519436552391055 140353303418279154828586583)
        ·
          refine ⟨210529955127418732242879875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140353303418279154828586583 210529955127418732242879875)
          ·
            refine ⟨315794932691128098364319813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210529955127418732242879875 315794932691128098364319813)
            ·
              refine ⟨59211549879586518443309965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 315794932691128098364319813 59211549879586518443309965)
              ·
                refine ⟨22204331204844944416241237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59211549879586518443309965 22204331204844944416241237)
                ·
                  refine ⟨260207006306776692377827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22204331204844944416241237 260207006306776692377827)
                  ·
                    rfl

theorem cell23_4560762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 8].length) (baseStart_4560762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560762 prefixEnd_4560762 := by exact prefixLift 4560762
  have htrace : WordTrace (prefixWord ++ tailWord_4560762) baseStart_4560762 baseEnd_4560762 := by
    simpa [prefixWord, tailWord_4560762, baseEnd_4560762] using wordTrace_append hprefix tailTrace_4560762
  have hstable : (prefixWord ++ tailWord_4560762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560762).length < 2 ^ (prefixWord ++ tailWord_4560762).sum := by decide
  have hdescent : baseEnd_4560762 < baseStart_4560762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560790 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_4560790 : Nat := 118140960795 + 4560790 * 2 ^ 59
def prefixEnd_4560790 : Nat := 4983230072969 + 3 ^ 40 * 4560790 * 2
def baseEnd_4560790 : Nat := 2341877434219316121850315

theorem tailTrace_4560790 : CollatzResearch.WordTrace tailWord_4560790 prefixEnd_4560790 2341877434219316121850315 := by
  unfold tailWord_4560790
  simp only [CollatzResearch.WordTrace]
  refine ⟨10396604821690264110252989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110897118098029483842698549 10396604821690264110252989)
  ·
    refine ⟨3898726808133849041344871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10396604821690264110252989 3898726808133849041344871)
    ·
      refine ⟨5848090212200773562017307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3898726808133849041344871 5848090212200773562017307)
      ·
        refine ⟨8772135318301160343025961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5848090212200773562017307 8772135318301160343025961)
        ·
          refine ⟨6579101488725870257269471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8772135318301160343025961 6579101488725870257269471)
          ·
            refine ⟨9868652233088805385904207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6579101488725870257269471 9868652233088805385904207)
            ·
              refine ⟨14802978349633208078856311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9868652233088805385904207 14802978349633208078856311)
              ·
                refine ⟨22204467524449812118284467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14802978349633208078856311 22204467524449812118284467)
                ·
                  refine ⟨33306701286674718177426701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22204467524449812118284467 33306701286674718177426701)
                  ·
                    refine ⟨12490012982503019316535013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33306701286674718177426701 12490012982503019316535013)
                    ·
                      refine ⟨2341877434219316121850315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12490012982503019316535013 2341877434219316121850315)
                      ·
                        rfl

theorem cell23_4560790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_4560790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560790 prefixEnd_4560790 := by exact prefixLift 4560790
  have htrace : WordTrace (prefixWord ++ tailWord_4560790) baseStart_4560790 baseEnd_4560790 := by
    simpa [prefixWord, tailWord_4560790, baseEnd_4560790] using wordTrace_append hprefix tailTrace_4560790
  have hstable : (prefixWord ++ tailWord_4560790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560790).length < 2 ^ (prefixWord ++ tailWord_4560790).sum := by decide
  have hdescent : baseEnd_4560790 < baseStart_4560790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560846 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2]
def baseStart_4560846 : Nat := 118140960795 + 4560846 * 2 ^ 59
def prefixEnd_4560846 : Nat := 4983230072969 + 3 ^ 40 * 4560846 * 2
def baseEnd_4560846 : Nat := 2341906189135967902750057

theorem tailTrace_4560846 : CollatzResearch.WordTrace tailWord_4560846 prefixEnd_4560846 2341906189135967902750057 := by
  unfold tailWord_4560846
  simp only [CollatzResearch.WordTrace]
  refine ⟨20793464954355168416010799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110898479756560898218724261 20793464954355168416010799)
  ·
    refine ⟨31190197431532752624016199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20793464954355168416010799 31190197431532752624016199)
    ·
      refine ⟨46785296147299128936024299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31190197431532752624016199 46785296147299128936024299)
      ·
        refine ⟨70177944220948693404036449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46785296147299128936024299 70177944220948693404036449)
        ·
          refine ⟨52633458165711520053027337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70177944220948693404036449 52633458165711520053027337)
          ·
            refine ⟨39475093624283640039770503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52633458165711520053027337 39475093624283640039770503)
            ·
              refine ⟨59212640436425460059655755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39475093624283640039770503 59212640436425460059655755)
              ·
                refine ⟨88818960654638190089483633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59212640436425460059655755 88818960654638190089483633)
                ·
                  refine ⟨66614220490978642567112725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88818960654638190089483633 66614220490978642567112725)
                  ·
                    refine ⟨3122541585514623870333409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66614220490978642567112725 3122541585514623870333409)
                    ·
                      refine ⟨2341906189135967902750057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3122541585514623870333409 2341906189135967902750057)
                      ·
                        rfl

theorem cell23_4560846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_4560846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560846 prefixEnd_4560846 := by exact prefixLift 4560846
  have htrace : WordTrace (prefixWord ++ tailWord_4560846) baseStart_4560846 baseEnd_4560846 := by
    simpa [prefixWord, tailWord_4560846, baseEnd_4560846] using wordTrace_append hprefix tailTrace_4560846
  have hstable : (prefixWord ++ tailWord_4560846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560846).length < 2 ^ (prefixWord ++ tailWord_4560846).sum := by decide
  have hdescent : baseEnd_4560846 < baseStart_4560846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560857 : List Nat := [1, 2, 1, 2, 6, 2, 1, 3, 1, 1, 3]
def baseStart_4560857 : Nat := 118140960795 + 4560857 * 2 ^ 59
def prefixEnd_4560857 : Nat := 4983230072969 + 3 ^ 40 * 4560857 * 2
def baseEnd_4560857 : Nat := 2341911837423167359712507

theorem tailTrace_4560857 : CollatzResearch.WordTrace tailWord_4560857 prefixEnd_4560857 2341911837423167359712507 := by
  unfold tailWord_4560857
  simp only [CollatzResearch.WordTrace]
  refine ⟨166348120837801496206736825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110898747225200997471157883 166348120837801496206736825)
  ·
    refine ⟨124761090628351122155052619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166348120837801496206736825 124761090628351122155052619)
    ·
      refine ⟨187141635942526683232578929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124761090628351122155052619 187141635942526683232578929)
      ·
        refine ⟨140356226956895012424434197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187141635942526683232578929 140356226956895012424434197)
        ·
          refine ⟨6579198138604453707395353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 140356226956895012424434197 6579198138604453707395353)
          ·
            refine ⟨4934398603953340280546515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6579198138604453707395353 4934398603953340280546515)
            ·
              refine ⟨7401597905930010420819773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4934398603953340280546515 7401597905930010420819773)
              ·
                refine ⟨2775599214723753907807415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7401597905930010420819773 2775599214723753907807415)
                ·
                  refine ⟨4163398822085630861711123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2775599214723753907807415 4163398822085630861711123)
                  ·
                    refine ⟨6245098233128446292566685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4163398822085630861711123 6245098233128446292566685)
                    ·
                      refine ⟨2341911837423167359712507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6245098233128446292566685 2341911837423167359712507)
                      ·
                        rfl

theorem cell23_4560857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 1, 1, 3].length) (baseStart_4560857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560857 prefixEnd_4560857 := by exact prefixLift 4560857
  have htrace : WordTrace (prefixWord ++ tailWord_4560857) baseStart_4560857 baseEnd_4560857 := by
    simpa [prefixWord, tailWord_4560857, baseEnd_4560857] using wordTrace_append hprefix tailTrace_4560857
  have hstable : (prefixWord ++ tailWord_4560857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560857).length < 2 ^ (prefixWord ++ tailWord_4560857).sum := by decide
  have hdescent : baseEnd_4560857 < baseStart_4560857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560880 : List Nat := [2, 1, 1, 1, 3, 2, 2, 6, 1, 2, 2]
def baseStart_4560880 : Nat := 118140960795 + 4560880 * 2 ^ 59
def prefixEnd_4560880 : Nat := 4983230072969 + 3 ^ 40 * 4560880 * 2
def baseEnd_4560880 : Nat := 2341923647478220769724901

theorem tailTrace_4560880 : CollatzResearch.WordTrace tailWord_4560880 prefixEnd_4560880 2341923647478220769724901 := by
  unfold tailWord_4560880
  simp only [CollatzResearch.WordTrace]
  refine ⟨83174479858359085567412047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110899306477812114089882729 83174479858359085567412047)
  ·
    refine ⟨124761719787538628351118071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83174479858359085567412047 124761719787538628351118071)
    ·
      refine ⟨187142579681307942526677107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124761719787538628351118071 187142579681307942526677107)
      ·
        refine ⟨280713869521961913790015661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187142579681307942526677107 280713869521961913790015661)
        ·
          refine ⟨105267701070735717671255873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 280713869521961913790015661 105267701070735717671255873)
          ·
            refine ⟨78950775803051788253441905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105267701070735717671255873 78950775803051788253441905)
            ·
              refine ⟨59213081852288841190081429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78950775803051788253441905 59213081852288841190081429)
              ·
                refine ⟨2775613211826039430785067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59213081852288841190081429 2775613211826039430785067)
                ·
                  refine ⟨4163419817739059146177601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2775613211826039430785067 4163419817739059146177601)
                  ·
                    refine ⟨3122564863304294359633201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4163419817739059146177601 3122564863304294359633201)
                    ·
                      refine ⟨2341923647478220769724901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3122564863304294359633201 2341923647478220769724901)
                      ·
                        rfl

theorem cell23_4560880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 1, 2, 2].length) (baseStart_4560880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560880 prefixEnd_4560880 := by exact prefixLift 4560880
  have htrace : WordTrace (prefixWord ++ tailWord_4560880) baseStart_4560880 baseEnd_4560880 := by
    simpa [prefixWord, tailWord_4560880, baseEnd_4560880] using wordTrace_append hprefix tailTrace_4560880
  have hstable : (prefixWord ++ tailWord_4560880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560880).length < 2 ^ (prefixWord ++ tailWord_4560880).sum := by decide
  have hdescent : baseEnd_4560880 < baseStart_4560880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560896 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 6, 1, 3]
def baseStart_4560896 : Nat := 118140960795 + 4560896 * 2 ^ 59
def prefixEnd_4560896 : Nat := 4983230072969 + 3 ^ 40 * 4560896 * 2
def baseEnd_4560896 : Nat := 2341931863168692707124827

theorem tailTrace_4560896 : CollatzResearch.WordTrace tailWord_4560896 prefixEnd_4560896 2341931863168692707124827 := by
  unfold tailWord_4560896
  simp only [CollatzResearch.WordTrace]
  refine ⟨83174771642330102933703271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110899695523106803911604361 83174771642330102933703271)
  ·
    refine ⟨124762157463495154400554907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83174771642330102933703271 124762157463495154400554907)
    ·
      refine ⟨187143236195242731600832361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124762157463495154400554907 187143236195242731600832361)
      ·
        refine ⟨140357427146432048700624271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187143236195242731600832361 140357427146432048700624271)
        ·
          refine ⟨210536140719648073050936407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140357427146432048700624271 210536140719648073050936407)
          ·
            refine ⟨315804211079472109576404611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210536140719648073050936407 315804211079472109576404611)
            ·
              refine ⟨473706316619208164364606917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315804211079472109576404611 473706316619208164364606917)
              ·
                refine ⟨88819934366101530818363797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 473706316619208164364606917 88819934366101530818363797)
                ·
                  refine ⟨4163434423411009257110803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88819934366101530818363797 4163434423411009257110803)
                  ·
                    refine ⟨6245151635116513885666205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4163434423411009257110803 6245151635116513885666205)
                    ·
                      refine ⟨2341931863168692707124827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6245151635116513885666205 2341931863168692707124827)
                      ·
                        rfl

theorem cell23_4560896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 6, 1, 3].length) (baseStart_4560896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560896 prefixEnd_4560896 := by exact prefixLift 4560896
  have htrace : WordTrace (prefixWord ++ tailWord_4560896) baseStart_4560896 baseEnd_4560896 := by
    simpa [prefixWord, tailWord_4560896, baseEnd_4560896] using wordTrace_append hprefix tailTrace_4560896
  have hstable : (prefixWord ++ tailWord_4560896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560896).length < 2 ^ (prefixWord ++ tailWord_4560896).sum := by decide
  have hdescent : baseEnd_4560896 < baseStart_4560896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560900 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4560900 : Nat := 118140960795 + 4560900 * 2 ^ 59
def prefixEnd_4560900 : Nat := 4983230072969 + 3 ^ 40 * 4560900 * 2
def baseEnd_4560900 : Nat := 2341933917091310691474809

theorem tailTrace_4560900 : CollatzResearch.WordTrace tailWord_4560900 prefixEnd_4560900 2341933917091310691474809 := by
  unfold tailWord_4560900
  simp only [CollatzResearch.WordTrace]
  refine ⟨83174844588322857275276077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110899792784430476367034769 83174844588322857275276077)
  ·
    refine ⟨31190566720621071478228529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83174844588322857275276077 31190566720621071478228529)
    ·
      refine ⟨23392925040465803608671397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31190566720621071478228529 23392925040465803608671397)
      ·
        refine ⟨4386173445087338176625887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23392925040465803608671397 4386173445087338176625887)
        ·
          refine ⟨6579260167631007264938831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4386173445087338176625887 6579260167631007264938831)
          ·
            refine ⟨9868890251446510897408247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6579260167631007264938831 9868890251446510897408247)
            ·
              refine ⟨14803335377169766346112371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9868890251446510897408247 14803335377169766346112371)
              ·
                refine ⟨22205003065754649519168557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14803335377169766346112371 22205003065754649519168557)
                ·
                  refine ⟨8326876149657993569688209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22205003065754649519168557 8326876149657993569688209)
                  ·
                    refine ⟨6245157112243495177266157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8326876149657993569688209 6245157112243495177266157)
                    ·
                      refine ⟨2341933917091310691474809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6245157112243495177266157 2341933917091310691474809)
                      ·
                        rfl

theorem cell23_4560900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4560900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560900 prefixEnd_4560900 := by exact prefixLift 4560900
  have htrace : WordTrace (prefixWord ++ tailWord_4560900) baseStart_4560900 baseEnd_4560900 := by
    simpa [prefixWord, tailWord_4560900, baseEnd_4560900] using wordTrace_append hprefix tailTrace_4560900
  have hstable : (prefixWord ++ tailWord_4560900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560900).length < 2 ^ (prefixWord ++ tailWord_4560900).sum := by decide
  have hdescent : baseEnd_4560900 < baseStart_4560900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560930 : List Nat := [3, 3, 1, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_4560930 : Nat := 118140960795 + 4560930 * 2 ^ 59
def prefixEnd_4560930 : Nat := 4983230072969 + 3 ^ 40 * 4560930 * 2
def baseEnd_4560930 : Nat := 2341949321510945574099671

theorem tailTrace_4560930 : CollatzResearch.WordTrace tailWord_4560930 prefixEnd_4560930 2341949321510945574099671 := by
  unfold tailWord_4560930
  simp only [CollatzResearch.WordTrace]
  refine ⟨41587695841634257418536061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110900522244358019782762829 41587695841634257418536061)
  ·
    refine ⟨15595385940612846531951023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41587695841634257418536061 15595385940612846531951023)
    ·
      refine ⟨23393078910919269797926535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15595385940612846531951023 23393078910919269797926535)
      ·
        refine ⟨35089618366378904696889803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23393078910919269797926535 35089618366378904696889803)
        ·
          refine ⟨52634427549568357045334705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35089618366378904696889803 52634427549568357045334705)
          ·
            refine ⟨39475820662176267784001029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52634427549568357045334705 39475820662176267784001029)
            ·
              refine ⟨7401716374158050209500193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39475820662176267784001029 7401716374158050209500193)
              ·
                refine ⟨5551287280618537657125145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7401716374158050209500193 5551287280618537657125145)
                ·
                  refine ⟨4163465460463903242843859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5551287280618537657125145 4163465460463903242843859)
                  ·
                    refine ⟨6245198190695854864265789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4163465460463903242843859 6245198190695854864265789)
                    ·
                      refine ⟨2341949321510945574099671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6245198190695854864265789 2341949321510945574099671)
                      ·
                        rfl

theorem cell23_4560930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_4560930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560930 prefixEnd_4560930 := by exact prefixLift 4560930
  have htrace : WordTrace (prefixWord ++ tailWord_4560930) baseStart_4560930 baseEnd_4560930 := by
    simpa [prefixWord, tailWord_4560930, baseEnd_4560930] using wordTrace_append hprefix tailTrace_4560930
  have hstable : (prefixWord ++ tailWord_4560930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560930).length < 2 ^ (prefixWord ++ tailWord_4560930).sum := by decide
  have hdescent : baseEnd_4560930 < baseStart_4560930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560939 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 5]
def baseStart_4560939 : Nat := 118140960795 + 4560939 * 2 ^ 59
def prefixEnd_4560939 : Nat := 4983230072969 + 3 ^ 40 * 4560939 * 2
def baseEnd_4560939 : Nat := 2341953942836836038887129

theorem tailTrace_4560939 : CollatzResearch.WordTrace tailWord_4560939 prefixEnd_4560939 2341953942836836038887129 := by
  unfold tailWord_4560939
  simp only [CollatzResearch.WordTrace]
  refine ⟨166351111623504424211221871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110900741082336282807481247 166351111623504424211221871)
  ·
    refine ⟨249526667435256636316832807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166351111623504424211221871 249526667435256636316832807)
    ·
      refine ⟨374290001152884954475249211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249526667435256636316832807 374290001152884954475249211)
      ·
        refine ⟨561435001729327431712873817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374290001152884954475249211 561435001729327431712873817)
        ·
          refine ⟨421076251296995573784655363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 561435001729327431712873817 421076251296995573784655363)
          ·
            refine ⟨631614376945493360676983045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421076251296995573784655363 631614376945493360676983045)
            ·
              refine ⟨118427695677280005126934321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 631614376945493360676983045 118427695677280005126934321)
              ·
                refine ⟨88820771757960003845200741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118427695677280005126934321 88820771757960003845200741)
                ·
                  refine ⟨16653894704617500720975139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88820771757960003845200741 16653894704617500720975139)
                  ·
                    refine ⟨24980842056926251081462709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16653894704617500720975139 24980842056926251081462709)
                    ·
                      refine ⟨2341953942836836038887129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24980842056926251081462709 2341953942836836038887129)
                      ·
                        rfl

theorem cell23_4560939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 5].length) (baseStart_4560939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560939 prefixEnd_4560939 := by exact prefixLift 4560939
  have htrace : WordTrace (prefixWord ++ tailWord_4560939) baseStart_4560939 baseEnd_4560939 := by
    simpa [prefixWord, tailWord_4560939, baseEnd_4560939] using wordTrace_append hprefix tailTrace_4560939
  have hstable : (prefixWord ++ tailWord_4560939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560939).length < 2 ^ (prefixWord ++ tailWord_4560939).sum := by decide
  have hdescent : baseEnd_4560939 < baseStart_4560939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560946 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 2, 6]
def baseStart_4560946 : Nat := 118140960795 + 4560946 * 2 ^ 59
def prefixEnd_4560946 : Nat := 4983230072969 + 3 ^ 40 * 4560946 * 2
def baseEnd_4560946 : Nat := 780652512400472503833199

theorem tailTrace_4560946 : CollatzResearch.WordTrace tailWord_4560946 prefixEnd_4560946 780652512400472503833199 := by
  unfold tailWord_4560946
  simp only [CollatzResearch.WordTrace]
  refine ⟨41587841733619766101681673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110900911289652709604484461 41587841733619766101681673)
  ·
    refine ⟨31190881300214824576261255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41587841733619766101681673 31190881300214824576261255)
    ·
      refine ⟨46786321950322236864391883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31190881300214824576261255 46786321950322236864391883)
      ·
        refine ⟨70179482925483355296587825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46786321950322236864391883 70179482925483355296587825)
        ·
          refine ⟨52634612194112516472440869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70179482925483355296587825 52634612194112516472440869)
          ·
            refine ⟨9868989786396096838582663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52634612194112516472440869 9868989786396096838582663)
            ·
              refine ⟨14803484679594145257873995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9868989786396096838582663 14803484679594145257873995)
              ·
                refine ⟨22205227019391217886810993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14803484679594145257873995 22205227019391217886810993)
                ·
                  refine ⟨16653920264543413415108245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22205227019391217886810993 16653920264543413415108245)
                  ·
                    refine ⟨780652512400472503833199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16653920264543413415108245 780652512400472503833199)
                    ·
                      rfl

theorem cell23_4560946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_4560946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560946 prefixEnd_4560946 := by exact prefixLift 4560946
  have htrace : WordTrace (prefixWord ++ tailWord_4560946) baseStart_4560946 baseEnd_4560946 := by
    simpa [prefixWord, tailWord_4560946, baseEnd_4560946] using wordTrace_append hprefix tailTrace_4560946
  have hstable : (prefixWord ++ tailWord_4560946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560946).length < 2 ^ (prefixWord ++ tailWord_4560946).sum := by decide
  have hdescent : baseEnd_4560946 < baseStart_4560946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560956 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 2, 4, 3]
def baseStart_4560956 : Nat := 118140960795 + 4560956 * 2 ^ 59
def prefixEnd_4560956 : Nat := 4983230072969 + 3 ^ 40 * 4560956 * 2
def baseEnd_4560956 : Nat := 2341962672007962472374551

theorem tailTrace_4560956 : CollatzResearch.WordTrace tailWord_4560956 prefixEnd_4560956 2341962672007962472374551 := by
  unfold tailWord_4560956
  simp only [CollatzResearch.WordTrace]
  refine ⟨83175865832221418057295361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110901154442961890743060481 83175865832221418057295361)
  ·
    refine ⟨62381899374166063542971521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83175865832221418057295361 62381899374166063542971521)
    ·
      refine ⟨46786424530624547657228641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62381899374166063542971521 46786424530624547657228641)
      ·
        refine ⟨35089818397968410742921481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46786424530624547657228641 35089818397968410742921481)
        ·
          refine ⟨26317363798476308057191111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35089818397968410742921481 26317363798476308057191111)
          ·
            refine ⟨39476045697714462085786667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26317363798476308057191111 39476045697714462085786667)
            ·
              refine ⟨59214068546571693128680001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39476045697714462085786667 59214068546571693128680001)
              ·
                refine ⟨44410551409928769846510001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59214068546571693128680001 44410551409928769846510001)
                ·
                  refine ⟨33307913557446577384882501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44410551409928769846510001 33307913557446577384882501)
                  ·
                    refine ⟨6245233792021233259665469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33307913557446577384882501 6245233792021233259665469)
                    ·
                      refine ⟨2341962672007962472374551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6245233792021233259665469 2341962672007962472374551)
                      ·
                        rfl

theorem cell23_4560956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_4560956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560956 prefixEnd_4560956 := by exact prefixLift 4560956
  have htrace : WordTrace (prefixWord ++ tailWord_4560956) baseStart_4560956 baseEnd_4560956 := by
    simpa [prefixWord, tailWord_4560956, baseEnd_4560956] using wordTrace_append hprefix tailTrace_4560956
  have hstable : (prefixWord ++ tailWord_4560956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560956).length < 2 ^ (prefixWord ++ tailWord_4560956).sum := by decide
  have hdescent : baseEnd_4560956 < baseStart_4560956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560959 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 9]
def baseStart_4560959 : Nat := 118140960795 + 4560959 * 2 ^ 59
def prefixEnd_4560959 : Nat := 4983230072969 + 3 ^ 40 * 4560959 * 2
def baseEnd_4560959 : Nat := 260218245827769551181893

theorem tailTrace_4560959 : CollatzResearch.WordTrace tailWord_4560959 prefixEnd_4560959 260218245827769551181893 := by
  unfold tailWord_4560959
  simp only [CollatzResearch.WordTrace]
  refine ⟨166351841083431967626949931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110901227388954645084633287 166351841083431967626949931)
  ·
    refine ⟨249527761625147951440424897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166351841083431967626949931 249527761625147951440424897)
    ·
      refine ⟨187145821218860963580318673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249527761625147951440424897 187145821218860963580318673)
      ·
        refine ⟨140359365914145722685239005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187145821218860963580318673 140359365914145722685239005)
        ·
          refine ⟨52634762217804646006964627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140359365914145722685239005 52634762217804646006964627)
          ·
            refine ⟨78952143326706969010446941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52634762217804646006964627 78952143326706969010446941)
            ·
              refine ⟨29607053747515113378917603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78952143326706969010446941 29607053747515113378917603)
              ·
                refine ⟨44410580621272670068376405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29607053747515113378917603 44410580621272670068376405)
                ·
                  refine ⟨260218245827769551181893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44410580621272670068376405 260218245827769551181893)
                  ·
                    rfl

theorem cell23_4560959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 9].length) (baseStart_4560959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560959 prefixEnd_4560959 := by exact prefixLift 4560959
  have htrace : WordTrace (prefixWord ++ tailWord_4560959) baseStart_4560959 baseEnd_4560959 := by
    simpa [prefixWord, tailWord_4560959, baseEnd_4560959] using wordTrace_append hprefix tailTrace_4560959
  have hstable : (prefixWord ++ tailWord_4560959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560959).length < 2 ^ (prefixWord ++ tailWord_4560959).sum := by decide
  have hdescent : baseEnd_4560959 < baseStart_4560959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4560986 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3]
def baseStart_4560986 : Nat := 118140960795 + 4560986 * 2 ^ 59
def prefixEnd_4560986 : Nat := 4983230072969 + 3 ^ 40 * 4560986 * 2
def baseEnd_4560986 : Nat := 2341978076427597354999413

theorem tailTrace_4560986 : CollatzResearch.WordTrace tailWord_4560986 prefixEnd_4560986 2341978076427597354999413 := by
  unfold tailWord_4560986
  simp only [CollatzResearch.WordTrace]
  refine ⟨41588206463583537809545703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110901883902889434158788541 41588206463583537809545703)
  ·
    refine ⟨62382309695375306714318555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41588206463583537809545703 62382309695375306714318555)
    ·
      refine ⟨93573464543062960071477833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62382309695375306714318555 93573464543062960071477833)
      ·
        refine ⟨70180098407297220053608375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93573464543062960071477833 70180098407297220053608375)
        ·
          refine ⟨105270147610945830080412563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70180098407297220053608375 105270147610945830080412563)
          ·
            refine ⟨157905221416418745120618845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105270147610945830080412563 157905221416418745120618845)
            ·
              refine ⟨59214458031157029420232067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157905221416418745120618845 59214458031157029420232067)
              ·
                refine ⟨88821687046735544130348101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59214458031157029420232067 88821687046735544130348101)
                ·
                  refine ⟨16654066321262914524440269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88821687046735544130348101 16654066321262914524440269)
                  ·
                    refine ⟨6245274870473592946665101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16654066321262914524440269 6245274870473592946665101)
                    ·
                      refine ⟨2341978076427597354999413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6245274870473592946665101 2341978076427597354999413)
                      ·
                        rfl

theorem cell23_4560986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_4560986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4560986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4560986 prefixEnd_4560986 := by exact prefixLift 4560986
  have htrace : WordTrace (prefixWord ++ tailWord_4560986) baseStart_4560986 baseEnd_4560986 := by
    simpa [prefixWord, tailWord_4560986, baseEnd_4560986] using wordTrace_append hprefix tailTrace_4560986
  have hstable : (prefixWord ++ tailWord_4560986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4560986).length < 2 ^ (prefixWord ++ tailWord_4560986).sum := by decide
  have hdescent : baseEnd_4560986 < baseStart_4560986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4560986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561006 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 3, 7]
def baseStart_4561006 : Nat := 118140960795 + 4561006 * 2 ^ 59
def prefixEnd_4561006 : Nat := 4983230072969 + 3 ^ 40 * 4561006 * 2
def baseEnd_4561006 : Nat := 780662782013562425583107

theorem tailTrace_4561006 : CollatzResearch.WordTrace tailWord_4561006 prefixEnd_4561006 780662782013562425583107 := by
  unfold tailWord_4561006
  simp only [CollatzResearch.WordTrace]
  refine ⟨20794194414282711831738859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110902370209507796435940581 20794194414282711831738859)
  ·
    refine ⟨31191291621424067747608289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20794194414282711831738859 31191291621424067747608289)
    ·
      refine ⟨23393468716068050810706217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31191291621424067747608289 23393468716068050810706217)
      ·
        refine ⟨17545101537051038108029663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23393468716068050810706217 17545101537051038108029663)
        ·
          refine ⟨26317652305576557162044495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17545101537051038108029663 26317652305576557162044495)
          ·
            refine ⟨39476478458364835743066743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26317652305576557162044495 39476478458364835743066743)
            ·
              refine ⟨59214717687547253614600115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39476478458364835743066743 59214717687547253614600115)
              ·
                refine ⟨88822076531320880421900173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59214717687547253614600115 88822076531320880421900173)
                ·
                  refine ⟨33308278699245330158212565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88822076531320880421900173 33308278699245330158212565)
                  ·
                    refine ⟨780662782013562425583107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33308278699245330158212565 780662782013562425583107)
                    ·
                      rfl

theorem cell23_4561006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_4561006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561006 prefixEnd_4561006 := by exact prefixLift 4561006
  have htrace : WordTrace (prefixWord ++ tailWord_4561006) baseStart_4561006 baseEnd_4561006 := by
    simpa [prefixWord, tailWord_4561006, baseEnd_4561006] using wordTrace_append hprefix tailTrace_4561006
  have hstable : (prefixWord ++ tailWord_4561006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561006).length < 2 ^ (prefixWord ++ tailWord_4561006).sum := by decide
  have hdescent : baseEnd_4561006 < baseStart_4561006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561044 : List Nat := [2, 4, 2, 3, 1, 1, 3, 2, 5]
def baseStart_4561044 : Nat := 118140960795 + 4561044 * 2 ^ 59
def prefixEnd_4561044 : Nat := 4983230072969 + 3 ^ 40 * 4561044 * 2
def baseEnd_4561044 : Nat := 260223095367284236452683

theorem tailTrace_4561044 : CollatzResearch.WordTrace tailWord_4561044 prefixEnd_4561044 260223095367284236452683 := by
  unfold tailWord_4561044
  simp only [CollatzResearch.WordTrace]
  refine ⟨83177470644062013571897093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110903294192082684762529457 83177470644062013571897093)
  ·
    refine ⟨15595775745761627544730705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83177470644062013571897093 15595775745761627544730705)
    ·
      refine ⟨11696831809321220658548029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15595775745761627544730705 11696831809321220658548029)
      ·
        refine ⟨4386311928495457746955511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11696831809321220658548029 4386311928495457746955511)
        ·
          refine ⟨6579467892743186620433267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4386311928495457746955511 6579467892743186620433267)
          ·
            refine ⟨9869201839114779930649901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6579467892743186620433267 9869201839114779930649901)
            ·
              refine ⟨3700950689668042473993713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9869201839114779930649901 3700950689668042473993713)
              ·
                refine ⟨2775713017251031855495285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3700950689668042473993713 2775713017251031855495285)
                ·
                  refine ⟨260223095367284236452683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2775713017251031855495285 260223095367284236452683)
                  ·
                    rfl

theorem cell23_4561044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_4561044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561044 prefixEnd_4561044 := by exact prefixLift 4561044
  have htrace : WordTrace (prefixWord ++ tailWord_4561044) baseStart_4561044 baseEnd_4561044 := by
    simpa [prefixWord, tailWord_4561044, baseEnd_4561044] using wordTrace_append hprefix tailTrace_4561044
  have hstable : (prefixWord ++ tailWord_4561044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561044).length < 2 ^ (prefixWord ++ tailWord_4561044).sum := by decide
  have hdescent : baseEnd_4561044 < baseStart_4561044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561077 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_4561077 : Nat := 118140960795 + 4561077 * 2 ^ 59
def prefixEnd_4561077 : Nat := 4983230072969 + 3 ^ 40 * 4561077 * 2
def baseEnd_4561077 : Nat := 2342024803167156498961495

theorem tailTrace_4561077 : CollatzResearch.WordTrace tailWord_4561077 prefixEnd_4561077 2342024803167156498961495 := by
  unfold tailWord_4561077
  simp only [CollatzResearch.WordTrace]
  refine ⟨166356144897004473779745485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110904096598002982519830323 166356144897004473779745485)
  ·
    refine ⟨62383554336376677667404557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166356144897004473779745485 62383554336376677667404557)
    ·
      refine ⟨23393832876141254125276709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62383554336376677667404557 23393832876141254125276709)
      ·
        refine ⟨4386343664276485148489383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23393832876141254125276709 4386343664276485148489383)
        ·
          refine ⟨6579515496414727722734075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4386343664276485148489383 6579515496414727722734075)
          ·
            refine ⟨9869273244622091584101113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6579515496414727722734075 9869273244622091584101113)
            ·
              refine ⟨7401954933466568688075835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9869273244622091584101113 7401954933466568688075835)
              ·
                refine ⟨11102932400199853032113753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7401954933466568688075835 11102932400199853032113753)
                ·
                  refine ⟨8327199300149889774085315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11102932400199853032113753 8327199300149889774085315)
                  ·
                    refine ⟨12490798950224834661127973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8327199300149889774085315 12490798950224834661127973)
                    ·
                      refine ⟨2342024803167156498961495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12490798950224834661127973 2342024803167156498961495)
                      ·
                        rfl

theorem cell23_4561077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_4561077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561077 prefixEnd_4561077 := by exact prefixLift 4561077
  have htrace : WordTrace (prefixWord ++ tailWord_4561077) baseStart_4561077 baseEnd_4561077 := by
    simpa [prefixWord, tailWord_4561077, baseEnd_4561077] using wordTrace_append hprefix tailTrace_4561077
  have hstable : (prefixWord ++ tailWord_4561077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561077).length < 2 ^ (prefixWord ++ tailWord_4561077).sum := by decide
  have hdescent : baseEnd_4561077 < baseStart_4561077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561127 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_4561127 : Nat := 118140960795 + 4561127 * 2 ^ 59
def prefixEnd_4561127 : Nat := 4983230072969 + 3 ^ 40 * 4561127 * 2
def baseEnd_4561127 : Nat := 2342050477199881303336265

theorem tailTrace_4561127 : CollatzResearch.WordTrace tailWord_4561127 prefixEnd_4561127 2342050477199881303336265 := by
  unfold tailWord_4561127
  simp only [CollatzResearch.WordTrace]
  refine ⟨166357968546823332319065635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110905312364548888212710423 166357968546823332319065635)
  ·
    refine ⟨249536952820234998478598453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166357968546823332319065635 249536952820234998478598453)
    ·
      refine ⟨23394089326897031107368605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 249536952820234998478598453 23394089326897031107368605)
      ·
        refine ⟨8772783497586386665263227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23394089326897031107368605 8772783497586386665263227)
        ·
          refine ⟨13159175246379579997894841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8772783497586386665263227 13159175246379579997894841)
          ·
            refine ⟨9869381434784684998421131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13159175246379579997894841 9869381434784684998421131)
            ·
              refine ⟨14804072152177027497631697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9869381434784684998421131 14804072152177027497631697)
              ·
                refine ⟨11103054114132770623223773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14804072152177027497631697 11103054114132770623223773)
                ·
                  refine ⟨4163645292799788983708915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11103054114132770623223773 4163645292799788983708915)
                  ·
                    refine ⟨6245467939199683475563373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4163645292799788983708915 6245467939199683475563373)
                    ·
                      refine ⟨2342050477199881303336265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6245467939199683475563373 2342050477199881303336265)
                      ·
                        rfl

theorem cell23_4561127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_4561127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561127 prefixEnd_4561127 := by exact prefixLift 4561127
  have htrace : WordTrace (prefixWord ++ tailWord_4561127) baseStart_4561127 baseEnd_4561127 := by
    simpa [prefixWord, tailWord_4561127, baseEnd_4561127] using wordTrace_append hprefix tailTrace_4561127
  have hstable : (prefixWord ++ tailWord_4561127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561127).length < 2 ^ (prefixWord ++ tailWord_4561127).sum := by decide
  have hdescent : baseEnd_4561127 < baseStart_4561127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561153 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_4561153 : Nat := 118140960795 + 4561153 * 2 ^ 59
def prefixEnd_4561153 : Nat := 4983230072969 + 3 ^ 40 * 4561153 * 2
def baseEnd_4561153 : Nat := 2342063827696898201611145

theorem tailTrace_4561153 : CollatzResearch.WordTrace tailWord_4561153 prefixEnd_4561153 2342063827696898201611145 := by
  unfold tailWord_4561153
  simp only [CollatzResearch.WordTrace]
  refine ⟨166358916844729138759512113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110905944563152759173008075 166358916844729138759512113)
  ·
    refine ⟨124769187633546854069634085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166358916844729138759512113 124769187633546854069634085)
    ·
      refine ⟨23394222681290035138056391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124769187633546854069634085 23394222681290035138056391)
      ·
        refine ⟨35091334021935052707084587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23394222681290035138056391 35091334021935052707084587)
        ·
          refine ⟨52637001032902579060626881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35091334021935052707084587 52637001032902579060626881)
          ·
            refine ⟨39477750774676934295470161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52637001032902579060626881 39477750774676934295470161)
            ·
              refine ⟨29608313081007700721602621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39477750774676934295470161 29608313081007700721602621)
              ·
                refine ⟨11103117405377887770600983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29608313081007700721602621 11103117405377887770600983)
                ·
                  refine ⟨16654676108066831655901475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11103117405377887770600983 16654676108066831655901475)
                  ·
                    refine ⟨24982014162100247483852213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16654676108066831655901475 24982014162100247483852213)
                    ·
                      refine ⟨2342063827696898201611145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24982014162100247483852213 2342063827696898201611145)
                      ·
                        rfl

theorem cell23_4561153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_4561153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561153 prefixEnd_4561153 := by exact prefixLift 4561153
  have htrace : WordTrace (prefixWord ++ tailWord_4561153) baseStart_4561153 baseEnd_4561153 := by
    simpa [prefixWord, tailWord_4561153, baseEnd_4561153] using wordTrace_append hprefix tailTrace_4561153
  have hstable : (prefixWord ++ tailWord_4561153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561153).length < 2 ^ (prefixWord ++ tailWord_4561153).sum := by decide
  have hdescent : baseEnd_4561153 < baseStart_4561153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561160 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 4, 4]
def baseStart_4561160 : Nat := 118140960795 + 4561160 * 2 ^ 59
def prefixEnd_4561160 : Nat := 4983230072969 + 3 ^ 40 * 4561160 * 2
def baseEnd_4561160 : Nat := 780689140687159891407871

theorem tailTrace_4561160 : CollatzResearch.WordTrace tailWord_4561160 prefixEnd_4561160 780689140687159891407871 := by
  unfold tailWord_4561160
  simp only [CollatzResearch.WordTrace]
  refine ⟨83179586077851889477508467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110906114770469185970011289 83179586077851889477508467)
  ·
    refine ⟨124769379116777834216262701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83179586077851889477508467 124769379116777834216262701)
    ·
      refine ⟨46788517168791687831098513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124769379116777834216262701 46788517168791687831098513)
      ·
        refine ⟨35091387876593765873323885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46788517168791687831098513 35091387876593765873323885)
        ·
          refine ⟨13159270453722662202496457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35091387876593765873323885 13159270453722662202496457)
          ·
            refine ⟨9869452840291996651872343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13159270453722662202496457 9869452840291996651872343)
            ·
              refine ⟨14804179260437994977808515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9869452840291996651872343 14804179260437994977808515)
              ·
                refine ⟨22206268890656992466712773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14804179260437994977808515 22206268890656992466712773)
                ·
                  refine ⟨4163675416998186087508645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22206268890656992466712773 4163675416998186087508645)
                  ·
                    refine ⟨780689140687159891407871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4163675416998186087508645 780689140687159891407871)
                    ·
                      rfl

theorem cell23_4561160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_4561160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561160 prefixEnd_4561160 := by exact prefixLift 4561160
  have htrace : WordTrace (prefixWord ++ tailWord_4561160) baseStart_4561160 baseEnd_4561160 := by
    simpa [prefixWord, tailWord_4561160, baseEnd_4561160] using wordTrace_append hprefix tailTrace_4561160
  have hstable : (prefixWord ++ tailWord_4561160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561160).length < 2 ^ (prefixWord ++ tailWord_4561160).sum := by decide
  have hdescent : baseEnd_4561160 < baseStart_4561160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561223 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_4561223 : Nat := 118140960795 + 4561223 * 2 ^ 59
def prefixEnd_4561223 : Nat := 4983230072969 + 3 ^ 40 * 4561223 * 2
def baseEnd_4561223 : Nat := 2342099771342712927735823

theorem tailTrace_4561223 : CollatzResearch.WordTrace tailWord_4561223 prefixEnd_4561223 2342099771342712927735823 := by
  unfold tailWord_4561223
  simp only [CollatzResearch.WordTrace]
  refine ⟨166361469954475540714560323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110907646636317027143040215 166361469954475540714560323)
  ·
    refine ⟨249542204931713311071840485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166361469954475540714560323 249542204931713311071840485)
    ·
      refine ⟨46789163424696245825970091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 249542204931713311071840485 46789163424696245825970091)
      ·
        refine ⟨70183745137044368738955137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46789163424696245825970091 70183745137044368738955137)
        ·
          refine ⟨52637808852783276554216353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70183745137044368738955137 52637808852783276554216353)
          ·
            refine ⟨39478356639587457415662265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52637808852783276554216353 39478356639587457415662265)
            ·
              refine ⟨29608767479690593061746699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39478356639587457415662265 29608767479690593061746699)
              ·
                refine ⟨44413151219535889592620049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29608767479690593061746699 44413151219535889592620049)
                ·
                  refine ⟨33309863414651917194465037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44413151219535889592620049 33309863414651917194465037)
                  ·
                    refine ⟨12491198780494468947924389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33309863414651917194465037 12491198780494468947924389)
                    ·
                      refine ⟨2342099771342712927735823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12491198780494468947924389 2342099771342712927735823)
                      ·
                        rfl

theorem cell23_4561223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_4561223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561223 prefixEnd_4561223 := by exact prefixLift 4561223
  have htrace : WordTrace (prefixWord ++ tailWord_4561223) baseStart_4561223 baseEnd_4561223 := by
    simpa [prefixWord, tailWord_4561223, baseEnd_4561223] using wordTrace_append hprefix tailTrace_4561223
  have hstable : (prefixWord ++ tailWord_4561223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561223).length < 2 ^ (prefixWord ++ tailWord_4561223).sum := by decide
  have hdescent : baseEnd_4561223 < baseStart_4561223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561234 : List Nat := [3, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3]
def baseStart_4561234 : Nat := 118140960795 + 4561234 * 2 ^ 59
def prefixEnd_4561234 : Nat := 4983230072969 + 3 ^ 40 * 4561234 * 2
def baseEnd_4561234 : Nat := 2342105419629912384698273

theorem tailTrace_4561234 : CollatzResearch.WordTrace tailWord_4561234 prefixEnd_4561234 2342105419629912384698273 := by
  unfold tailWord_4561234
  simp only [CollatzResearch.WordTrace]
  refine ⟨41590467789358922398302689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110907914104957126395473837 41590467789358922398302689)
  ·
    refine ⟨31192850842019191798727017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41590467789358922398302689 31192850842019191798727017)
    ·
      refine ⟨23394638131514393849045263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31192850842019191798727017 23394638131514393849045263)
      ·
        refine ⟨35091957197271590773567895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23394638131514393849045263 35091957197271590773567895)
        ·
          refine ⟨52637935795907386160351843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35091957197271590773567895 52637935795907386160351843)
          ·
            refine ⟨78956903693861079240527765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52637935795907386160351843 78956903693861079240527765)
            ·
              refine ⟨3701104860649738089399739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78956903693861079240527765 3701104860649738089399739)
              ·
                refine ⟨5551657290974607134099609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3701104860649738089399739 5551657290974607134099609)
                ·
                  refine ⟨4163742968230955350574707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5551657290974607134099609 4163742968230955350574707)
                  ·
                    refine ⟨6245614452346433025862061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4163742968230955350574707 6245614452346433025862061)
                    ·
                      refine ⟨2342105419629912384698273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6245614452346433025862061 2342105419629912384698273)
                      ·
                        rfl

theorem cell23_4561234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_4561234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561234 prefixEnd_4561234 := by exact prefixLift 4561234
  have htrace : WordTrace (prefixWord ++ tailWord_4561234) baseStart_4561234 baseEnd_4561234 := by
    simpa [prefixWord, tailWord_4561234, baseEnd_4561234] using wordTrace_append hprefix tailTrace_4561234
  have hstable : (prefixWord ++ tailWord_4561234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561234).length < 2 ^ (prefixWord ++ tailWord_4561234).sum := by decide
  have hdescent : baseEnd_4561234 < baseStart_4561234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561303 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 7]
def baseStart_4561303 : Nat := 118140960795 + 4561303 * 2 ^ 59
def prefixEnd_4561303 : Nat := 4983230072969 + 3 ^ 40 * 4561303 * 2
def baseEnd_4561303 : Nat := 2342140849795072614735455

theorem tailTrace_4561303 : CollatzResearch.WordTrace tailWord_4561303 prefixEnd_4561303 2342140849795072614735455 := by
  unfold tailWord_4561303
  simp only [CollatzResearch.WordTrace]
  refine ⟨166364387794185714377472563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110909591862790476251648375 166364387794185714377472563)
  ·
    refine ⟨249546581691278571566208845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166364387794185714377472563 249546581691278571566208845)
    ·
      refine ⟨93579968134229464337328317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249546581691278571566208845 93579968134229464337328317)
      ·
        refine ⟨35092488050336049126498119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93579968134229464337328317 35092488050336049126498119)
        ·
          refine ⟨52638732075504073689747179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35092488050336049126498119 52638732075504073689747179)
          ·
            refine ⟨78958098113256110534620769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52638732075504073689747179 78958098113256110534620769)
            ·
              refine ⟨59218573584942082900965577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78958098113256110534620769 59218573584942082900965577)
              ·
                refine ⟨44413930188706562175724183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59218573584942082900965577 44413930188706562175724183)
                ·
                  refine ⟨66620895283059843263586275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44413930188706562175724183 66620895283059843263586275)
                  ·
                    refine ⟨99931342924589764895379413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66620895283059843263586275 99931342924589764895379413)
                    ·
                      refine ⟨2342140849795072614735455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99931342924589764895379413 2342140849795072614735455)
                      ·
                        rfl

theorem cell23_4561303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_4561303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561303 prefixEnd_4561303 := by exact prefixLift 4561303
  have htrace : WordTrace (prefixWord ++ tailWord_4561303) baseStart_4561303 baseEnd_4561303 := by
    simpa [prefixWord, tailWord_4561303, baseEnd_4561303] using wordTrace_append hprefix tailTrace_4561303
  have hstable : (prefixWord ++ tailWord_4561303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561303).length < 2 ^ (prefixWord ++ tailWord_4561303).sum := by decide
  have hdescent : baseEnd_4561303 < baseStart_4561303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561325 : List Nat := [1, 5, 2, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_4561325 : Nat := 118140960795 + 4561325 * 2 ^ 59
def prefixEnd_4561325 : Nat := 4983230072969 + 3 ^ 40 * 4561325 * 2
def baseEnd_4561325 : Nat := 2342152146369471528660355

theorem tailTrace_4561325 : CollatzResearch.WordTrace tailWord_4561325 prefixEnd_4561325 2342152146369471528660355 := by
  unfold tailWord_4561325
  simp only [CollatzResearch.WordTrace]
  refine ⟨166365190200106012134773429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110910126800070674756515619 166365190200106012134773429)
  ·
    refine ⟨15596736581259938637635009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166365190200106012134773429 15596736581259938637635009)
    ·
      refine ⟨11697552435944953978226257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15596736581259938637635009 11697552435944953978226257)
      ·
        refine ⟨8773164326958715483669693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11697552435944953978226257 8773164326958715483669693)
        ·
          refine ⟨3289936622609518306376135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8773164326958715483669693 3289936622609518306376135)
          ·
            refine ⟨4934904933914277459564203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3289936622609518306376135 4934904933914277459564203)
            ·
              refine ⟨7402357400871416189346305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4934904933914277459564203 7402357400871416189346305)
              ·
                refine ⟨5551768050653562142009729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7402357400871416189346305 5551768050653562142009729)
                ·
                  refine ⟨4163826037990171606507297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5551768050653562142009729 4163826037990171606507297)
                  ·
                    refine ⟨3122869528492628704880473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4163826037990171606507297 3122869528492628704880473)
                    ·
                      refine ⟨2342152146369471528660355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3122869528492628704880473 2342152146369471528660355)
                      ·
                        rfl

theorem cell23_4561325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_4561325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561325 prefixEnd_4561325 := by exact prefixLift 4561325
  have htrace : WordTrace (prefixWord ++ tailWord_4561325) baseStart_4561325 baseEnd_4561325 := by
    simpa [prefixWord, tailWord_4561325, baseEnd_4561325] using wordTrace_append hprefix tailTrace_4561325
  have hstable : (prefixWord ++ tailWord_4561325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561325).length < 2 ^ (prefixWord ++ tailWord_4561325).sum := by decide
  have hdescent : baseEnd_4561325 < baseStart_4561325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561330 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_4561330 : Nat := 118140960795 + 4561330 * 2 ^ 59
def prefixEnd_4561330 : Nat := 4983230072969 + 3 ^ 40 * 4561330 * 2
def baseEnd_4561330 : Nat := 2342154713772744009097831

theorem tailTrace_4561330 : CollatzResearch.WordTrace tailWord_4561330 prefixEnd_4561330 2342154713772744009097831 := by
  unfold tailWord_4561330
  simp only [CollatzResearch.WordTrace]
  refine ⟨41591343141271974497176361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110910248376725265325803629 41591343141271974497176361)
  ·
    refine ⟨31193507355953980872882271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41591343141271974497176361 31193507355953980872882271)
    ·
      refine ⟨46790261033930971309323407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31193507355953980872882271 46790261033930971309323407)
      ·
        refine ⟨70185391550896456963985111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46790261033930971309323407 70185391550896456963985111)
        ·
          refine ⟨105278087326344685445977667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70185391550896456963985111 105278087326344685445977667)
          ·
            refine ⟨157917130989517028168966501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105278087326344685445977667 157917130989517028168966501)
            ·
              refine ⟨29609462060534442781681219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157917130989517028168966501 29609462060534442781681219)
              ·
                refine ⟨44414193090801664172521829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29609462060534442781681219 44414193090801664172521829)
                ·
                  refine ⟨8327661204525312032347843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44414193090801664172521829 8327661204525312032347843)
                  ·
                    refine ⟨12491491806787968048521765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8327661204525312032347843 12491491806787968048521765)
                    ·
                      refine ⟨2342154713772744009097831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12491491806787968048521765 2342154713772744009097831)
                      ·
                        rfl

theorem cell23_4561330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_4561330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561330 prefixEnd_4561330 := by exact prefixLift 4561330
  have htrace : WordTrace (prefixWord ++ tailWord_4561330) baseStart_4561330 baseEnd_4561330 := by
    simpa [prefixWord, tailWord_4561330, baseEnd_4561330] using wordTrace_append hprefix tailTrace_4561330
  have hstable : (prefixWord ++ tailWord_4561330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561330).length < 2 ^ (prefixWord ++ tailWord_4561330).sum := by decide
  have hdescent : baseEnd_4561330 < baseStart_4561330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561400 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 3, 5]
def baseStart_4561400 : Nat := 118140960795 + 4561400 * 2 ^ 59
def prefixEnd_4561400 : Nat := 4983230072969 + 3 ^ 40 * 4561400 * 2
def baseEnd_4561400 : Nat := 780730219139519578407503

theorem tailTrace_4561400 : CollatzResearch.WordTrace tailWord_4561400 prefixEnd_4561400 780730219139519578407503 := by
  unfold tailWord_4561400
  simp only [CollatzResearch.WordTrace]
  refine ⟨83183962837417149971876827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110911950449889533295835769 83183962837417149971876827)
  ·
    refine ⟨124775944256125724957815241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83183962837417149971876827 124775944256125724957815241)
    ·
      refine ⟨93581958192094293718361431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124775944256125724957815241 93581958192094293718361431)
      ·
        refine ⟨140372937288141440577542147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93581958192094293718361431 140372937288141440577542147)
        ·
          refine ⟨210559405932212160866313221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140372937288141440577542147 210559405932212160866313221)
          ·
            refine ⟨39479888612289780162433729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210559405932212160866313221 39479888612289780162433729)
            ·
              refine ⟨29609916459217335121825297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39479888612289780162433729 29609916459217335121825297)
              ·
                refine ⟨22207437344413001341368973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29609916459217335121825297 22207437344413001341368973)
                ·
                  refine ⟨8327789004154875503013365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22207437344413001341368973 8327789004154875503013365)
                  ·
                    refine ⟨780730219139519578407503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8327789004154875503013365 780730219139519578407503)
                    ·
                      rfl

theorem cell23_4561400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_4561400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561400 prefixEnd_4561400 := by exact prefixLift 4561400
  have htrace : WordTrace (prefixWord ++ tailWord_4561400) baseStart_4561400 baseEnd_4561400 := by
    simpa [prefixWord, tailWord_4561400, baseEnd_4561400] using wordTrace_append hprefix tailTrace_4561400
  have hstable : (prefixWord ++ tailWord_4561400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561400).length < 2 ^ (prefixWord ++ tailWord_4561400).sum := by decide
  have hdescent : baseEnd_4561400 < baseStart_4561400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561407 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 4, 3, 2]
def baseStart_4561407 : Nat := 118140960795 + 4561407 * 2 ^ 59
def prefixEnd_4561407 : Nat := 4983230072969 + 3 ^ 40 * 4561407 * 2
def baseEnd_4561407 : Nat := 2342194251783140207834977

theorem tailTrace_4561407 : CollatzResearch.WordTrace tailWord_4561407 prefixEnd_4561407 2342194251783140207834977 := by
  unfold tailWord_4561407
  simp only [CollatzResearch.WordTrace]
  refine ⟨166368180985808940139258475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110912120657205960092838983 166368180985808940139258475)
  ·
    refine ⟨249552271478713410208887713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166368180985808940139258475 249552271478713410208887713)
    ·
      refine ⟨187164203609035057656665785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249552271478713410208887713 187164203609035057656665785)
      ·
        refine ⟨140373152706776293242499339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187164203609035057656665785 140373152706776293242499339)
        ·
          refine ⟨210559729060164439863749009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140373152706776293242499339 210559729060164439863749009)
          ·
            refine ⟨157919796795123329897811757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210559729060164439863749009 157919796795123329897811757)
            ·
              refine ⟨59219923798171248711679409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157919796795123329897811757 59219923798171248711679409)
              ·
                refine ⟨44414942848628436533759557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59219923798171248711679409 44414942848628436533759557)
                ·
                  refine ⟨8327801784117831850079917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44414942848628436533759557 8327801784117831850079917)
                  ·
                    refine ⟨3122925669044186943779969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8327801784117831850079917 3122925669044186943779969)
                    ·
                      refine ⟨2342194251783140207834977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3122925669044186943779969 2342194251783140207834977)
                      ·
                        rfl

theorem cell23_4561407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 3, 2].length) (baseStart_4561407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561407 prefixEnd_4561407 := by exact prefixLift 4561407
  have htrace : WordTrace (prefixWord ++ tailWord_4561407) baseStart_4561407 baseEnd_4561407 := by
    simpa [prefixWord, tailWord_4561407, baseEnd_4561407] using wordTrace_append hprefix tailTrace_4561407
  have hstable : (prefixWord ++ tailWord_4561407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561407).length < 2 ^ (prefixWord ++ tailWord_4561407).sum := by decide
  have hdescent : baseEnd_4561407 < baseStart_4561407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561448 : List Nat := [2, 1, 5, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_4561448 : Nat := 118140960795 + 4561448 * 2 ^ 59
def prefixEnd_4561448 : Nat := 4983230072969 + 3 ^ 40 * 4561448 * 2
def baseEnd_4561448 : Nat := 2342215304489974547422289

theorem tailTrace_4561448 : CollatzResearch.WordTrace tailWord_4561448 prefixEnd_4561448 2342215304489974547422289 := by
  unfold tailWord_4561448
  simp only [CollatzResearch.WordTrace]
  refine ⟨83184838189330202070750499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110913117585773602761000665 83184838189330202070750499)
  ·
    refine ⟨124777257283995303106125749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83184838189330202070750499 124777257283995303106125749)
    ·
      refine ⟨11697867870374559666199289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124777257283995303106125749 11697867870374559666199289)
      ·
        refine ⟨8773400902780919749649467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11697867870374559666199289 8773400902780919749649467)
        ·
          refine ⟨13160101354171379624474201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8773400902780919749649467 13160101354171379624474201)
          ·
            refine ⟨9870076015628534718355651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13160101354171379624474201 9870076015628534718355651)
            ·
              refine ⟨14805114023442802077533477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9870076015628534718355651 14805114023442802077533477)
              ·
                refine ⟨2775958879395525389537527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14805114023442802077533477 2775958879395525389537527)
                ·
                  refine ⟨4163938319093288084306291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2775958879395525389537527 4163938319093288084306291)
                  ·
                    refine ⟨6245907478639932126459437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4163938319093288084306291 6245907478639932126459437)
                    ·
                      refine ⟨2342215304489974547422289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6245907478639932126459437 2342215304489974547422289)
                      ·
                        rfl

theorem cell23_4561448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_4561448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561448 prefixEnd_4561448 := by exact prefixLift 4561448
  have htrace : WordTrace (prefixWord ++ tailWord_4561448) baseStart_4561448 baseEnd_4561448 := by
    simpa [prefixWord, tailWord_4561448, baseEnd_4561448] using wordTrace_append hprefix tailTrace_4561448
  have hstable : (prefixWord ++ tailWord_4561448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561448).length < 2 ^ (prefixWord ++ tailWord_4561448).sum := by decide
  have hdescent : baseEnd_4561448 < baseStart_4561448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561457 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 3, 2, 3]
def baseStart_4561457 : Nat := 118140960795 + 4561457 * 2 ^ 59
def prefixEnd_4561457 : Nat := 4983230072969 + 3 ^ 40 * 4561457 * 2
def baseEnd_4561457 : Nat := 2342219925815865012209747

theorem tailTrace_4561457 : CollatzResearch.WordTrace tailWord_4561457 prefixEnd_4561457 2342219925815865012209747 := by
  unfold tailWord_4561457
  simp only [CollatzResearch.WordTrace]
  refine ⟨166370004635627798678578625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110913336423751865785719083 166370004635627798678578625)
  ·
    refine ⟨124777503476720849008933969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166370004635627798678578625 124777503476720849008933969)
    ·
      refine ⟨93583127607540636756700477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124777503476720849008933969 93583127607540636756700477)
      ·
        refine ⟨35093672852827738783762679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93583127607540636756700477 35093672852827738783762679)
        ·
          refine ⟨52640509279241608175644019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35093672852827738783762679 52640509279241608175644019)
          ·
            refine ⟨78960763918862412263466029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52640509279241608175644019 78960763918862412263466029)
            ·
              refine ⟨29610286469573404598799761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78960763918862412263466029 29610286469573404598799761)
              ·
                refine ⟨22207714852180053449099821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29610286469573404598799761 22207714852180053449099821)
                ·
                  refine ⟨8327893069567520043412433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22207714852180053449099821 8327893069567520043412433)
                  ·
                    refine ⟨6245919802175640032559325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8327893069567520043412433 6245919802175640032559325)
                    ·
                      refine ⟨2342219925815865012209747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6245919802175640032559325 2342219925815865012209747)
                      ·
                        rfl

theorem cell23_4561457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_4561457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561457 prefixEnd_4561457 := by exact prefixLift 4561457
  have htrace : WordTrace (prefixWord ++ tailWord_4561457) baseStart_4561457 baseEnd_4561457 := by
    simpa [prefixWord, tailWord_4561457, baseEnd_4561457] using wordTrace_append hprefix tailTrace_4561457
  have hstable : (prefixWord ++ tailWord_4561457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561457).length < 2 ^ (prefixWord ++ tailWord_4561457).sum := by decide
  have hdescent : baseEnd_4561457 < baseStart_4561457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561477 : List Nat := [1, 3, 1, 1, 1, 6, 3, 7]
def baseStart_4561477 : Nat := 118140960795 + 4561477 * 2 ^ 59
def prefixEnd_4561477 : Nat := 4983230072969 + 3 ^ 40 * 4561477 * 2
def baseEnd_4561477 : Nat := 86749266497368701257765

theorem tailTrace_4561477 : CollatzResearch.WordTrace tailWord_4561477 prefixEnd_4561477 86749266497368701257765 := by
  unfold tailWord_4561477
  simp only [CollatzResearch.WordTrace]
  refine ⟨166370734095555342094306685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110913822730370228062871123 166370734095555342094306685)
  ·
    refine ⟨62389025285833253285365007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166370734095555342094306685 62389025285833253285365007)
    ·
      refine ⟨93583537928749879928047511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62389025285833253285365007 93583537928749879928047511)
      ·
        refine ⟨140375306893124819892071267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93583537928749879928047511 140375306893124819892071267)
        ·
          refine ⟨210562960339687229838106901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140375306893124819892071267 210562960339687229838106901)
          ·
            refine ⟨9870138765922838898661261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 210562960339687229838106901 9870138765922838898661261)
            ·
              refine ⟨3701302037221064586997973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9870138765922838898661261 3701302037221064586997973)
              ·
                refine ⟨86749266497368701257765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3701302037221064586997973 86749266497368701257765)
                ·
                  rfl

theorem cell23_4561477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 7].length) (baseStart_4561477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561477 prefixEnd_4561477 := by exact prefixLift 4561477
  have htrace : WordTrace (prefixWord ++ tailWord_4561477) baseStart_4561477 baseEnd_4561477 := by
    simpa [prefixWord, tailWord_4561477, baseEnd_4561477] using wordTrace_append hprefix tailTrace_4561477
  have hstable : (prefixWord ++ tailWord_4561477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561477).length < 2 ^ (prefixWord ++ tailWord_4561477).sum := by decide
  have hdescent : baseEnd_4561477 < baseStart_4561477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561487 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 3]
def baseStart_4561487 : Nat := 118140960795 + 4561487 * 2 ^ 59
def prefixEnd_4561487 : Nat := 4983230072969 + 3 ^ 40 * 4561487 * 2
def baseEnd_4561487 : Nat := 2342235330235499894834609

theorem tailTrace_4561487 : CollatzResearch.WordTrace tailWord_4561487 prefixEnd_4561487 2342235330235499894834609 := by
  unfold tailWord_4561487
  simp only [CollatzResearch.WordTrace]
  refine ⟨166371098825519113802170715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110914065883679409201447143 166371098825519113802170715)
  ·
    refine ⟨249556648238278670703256073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166371098825519113802170715 249556648238278670703256073)
    ·
      refine ⟨187167486178709003027442055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249556648238278670703256073 187167486178709003027442055)
      ·
        refine ⟨280751229268063504541163083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187167486178709003027442055 280751229268063504541163083)
        ·
          refine ⟨421126843902095256811744625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280751229268063504541163083 421126843902095256811744625)
          ·
            refine ⟨315845132926571442608808469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421126843902095256811744625 315845132926571442608808469)
            ·
              refine ⟨14805240605933036372287897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 315845132926571442608808469 14805240605933036372287897)
              ·
                refine ⟨11103930454449777279215923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14805240605933036372287897 11103930454449777279215923)
                ·
                  refine ⟨16655895681674665918823885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11103930454449777279215923 16655895681674665918823885)
                  ·
                    refine ⟨6245960880627999719558957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16655895681674665918823885 6245960880627999719558957)
                    ·
                      refine ⟨2342235330235499894834609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6245960880627999719558957 2342235330235499894834609)
                      ·
                        rfl

theorem cell23_4561487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 3].length) (baseStart_4561487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561487 prefixEnd_4561487 := by exact prefixLift 4561487
  have htrace : WordTrace (prefixWord ++ tailWord_4561487) baseStart_4561487 baseEnd_4561487 := by
    simpa [prefixWord, tailWord_4561487, baseEnd_4561487] using wordTrace_append hprefix tailTrace_4561487
  have hstable : (prefixWord ++ tailWord_4561487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561487).length < 2 ^ (prefixWord ++ tailWord_4561487).sum := by decide
  have hdescent : baseEnd_4561487 < baseStart_4561487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561561 : List Nat := [1, 2, 1, 2, 1, 2, 4, 4, 2, 2, 2]
def baseStart_4561561 : Nat := 118140960795 + 4561561 * 2 ^ 59
def prefixEnd_4561561 : Nat := 4983230072969 + 3 ^ 40 * 4561561 * 2
def baseEnd_4561561 : Nat := 2342273327803932605309269

theorem tailTrace_4561561 : CollatzResearch.WordTrace tailWord_4561561 prefixEnd_4561561 2342273327803932605309269 := by
  unfold tailWord_4561561
  simp only [CollatzResearch.WordTrace]
  refine ⟨166373797827251024440364537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110915865218167349626909691 166373797827251024440364537)
  ·
    refine ⟨124780348370438268330273403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166373797827251024440364537 124780348370438268330273403)
    ·
      refine ⟨187170522555657402495410105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124780348370438268330273403 187170522555657402495410105)
      ·
        refine ⟨140377891916743051871557579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187170522555657402495410105 140377891916743051871557579)
        ·
          refine ⟨210566837875114577807336369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140377891916743051871557579 210566837875114577807336369)
          ·
            refine ⟨157925128406335933355502277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210566837875114577807336369 157925128406335933355502277)
            ·
              refine ⟨29610961576187987504156677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157925128406335933355502277 29610961576187987504156677)
              ·
                refine ⟨5552055295535247657029377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29610961576187987504156677 5552055295535247657029377)
                ·
                  refine ⟨4164041471651435742772033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5552055295535247657029377 4164041471651435742772033)
                  ·
                    refine ⟨3123031103738576807079025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4164041471651435742772033 3123031103738576807079025)
                    ·
                      refine ⟨2342273327803932605309269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3123031103738576807079025 2342273327803932605309269)
                      ·
                        rfl

theorem cell23_4561561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 2, 2].length) (baseStart_4561561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561561 prefixEnd_4561561 := by exact prefixLift 4561561
  have htrace : WordTrace (prefixWord ++ tailWord_4561561) baseStart_4561561 baseEnd_4561561 := by
    simpa [prefixWord, tailWord_4561561, baseEnd_4561561] using wordTrace_append hprefix tailTrace_4561561
  have hstable : (prefixWord ++ tailWord_4561561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561561).length < 2 ^ (prefixWord ++ tailWord_4561561).sum := by decide
  have hdescent : baseEnd_4561561 < baseStart_4561561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561614 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 2, 5]
def baseStart_4561614 : Nat := 118140960795 + 4561614 * 2 ^ 59
def prefixEnd_4561614 : Nat := 4983230072969 + 3 ^ 40 * 4561614 * 2
def baseEnd_4561614 : Nat := 780766847426206965982175

theorem tailTrace_4561614 : CollatzResearch.WordTrace tailWord_4561614 prefixEnd_4561614 780766847426206965982175 := by
  unfold tailWord_4561614
  simp only [CollatzResearch.WordTrace]
  refine ⟨20796966362007376811505487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110917153930706009661362597 20796966362007376811505487)
  ·
    refine ⟨31195449543011065217258231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20796966362007376811505487 31195449543011065217258231)
    ·
      refine ⟨46793174314516597825887347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31195449543011065217258231 46793174314516597825887347)
      ·
        refine ⟨70189761471774896738831021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46793174314516597825887347 70189761471774896738831021)
        ·
          refine ⟨26321160551915586277061633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70189761471774896738831021 26321160551915586277061633)
          ·
            refine ⟨19740870413936689707796225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26321160551915586277061633 19740870413936689707796225)
            ·
              refine ⟨14805652810452517280847169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19740870413936689707796225 14805652810452517280847169)
              ·
                refine ⟨11104239607839387960635377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14805652810452517280847169 11104239607839387960635377)
                ·
                  refine ⟨8328179705879540970476533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11104239607839387960635377 8328179705879540970476533)
                  ·
                    refine ⟨780766847426206965982175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8328179705879540970476533 780766847426206965982175)
                    ·
                      rfl

theorem cell23_4561614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_4561614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561614 prefixEnd_4561614 := by exact prefixLift 4561614
  have htrace : WordTrace (prefixWord ++ tailWord_4561614) baseStart_4561614 baseEnd_4561614 := by
    simpa [prefixWord, tailWord_4561614, baseEnd_4561614] using wordTrace_append hprefix tailTrace_4561614
  have hstable : (prefixWord ++ tailWord_4561614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561614).length < 2 ^ (prefixWord ++ tailWord_4561614).sum := by decide
  have hdescent : baseEnd_4561614 < baseStart_4561614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561701 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 3, 1, 3]
def baseStart_4561701 : Nat := 118140960795 + 4561701 * 2 ^ 59
def prefixEnd_4561701 : Nat := 4983230072969 + 3 ^ 40 * 4561701 * 2
def baseEnd_4561701 : Nat := 2342345215095562057558625

theorem tailTrace_4561701 : CollatzResearch.WordTrace tailWord_4561701 prefixEnd_4561701 2342345215095562057558625 := by
  unfold tailWord_4561701
  simp only [CollatzResearch.WordTrace]
  refine ⟨166378904046743828350460957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110919269364495885566973971 166378904046743828350460957)
  ·
    refine ⟨62392089017528935631422859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166378904046743828350460957 62392089017528935631422859)
    ·
      refine ⟨93588133526293403447134289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62392089017528935631422859 93588133526293403447134289)
      ·
        refine ⟨70191100144720052585350717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93588133526293403447134289 70191100144720052585350717)
        ·
          refine ⟨26321662554270019719506519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70191100144720052585350717 26321662554270019719506519)
          ·
            refine ⟨39482493831405029579259779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26321662554270019719506519 39482493831405029579259779)
            ·
              refine ⟨59223740747107544368889669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39482493831405029579259779 59223740747107544368889669)
              ·
                refine ⟨11104451390082664569166813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59223740747107544368889669 11104451390082664569166813)
                ·
                  refine ⟨4164169271280999213437555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11104451390082664569166813 4164169271280999213437555)
                  ·
                    refine ⟨6246253906921498820156333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4164169271280999213437555 6246253906921498820156333)
                    ·
                      refine ⟨2342345215095562057558625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6246253906921498820156333 2342345215095562057558625)
                      ·
                        rfl

theorem cell23_4561701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_4561701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561701 prefixEnd_4561701 := by exact prefixLift 4561701
  have htrace : WordTrace (prefixWord ++ tailWord_4561701) baseStart_4561701 baseEnd_4561701 := by
    simpa [prefixWord, tailWord_4561701, baseEnd_4561701] using wordTrace_append hprefix tailTrace_4561701
  have hstable : (prefixWord ++ tailWord_4561701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561701).length < 2 ^ (prefixWord ++ tailWord_4561701).sum := by decide
  have hdescent : baseEnd_4561701 < baseStart_4561701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561724 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_4561724 : Nat := 118140960795 + 4561724 * 2 ^ 59
def prefixEnd_4561724 : Nat := 4983230072969 + 3 ^ 40 * 4561724 * 2
def baseEnd_4561724 : Nat := 2342357025150615467571019

theorem tailTrace_4561724 : CollatzResearch.WordTrace tailWord_4561724 prefixEnd_4561724 2342357025150615467571019 := by
  unfold tailWord_4561724
  simp only [CollatzResearch.WordTrace]
  refine ⟨83189871462830251639274113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110919828617107002185698817 83189871462830251639274113)
  ·
    refine ⟨62392403597122688729455585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83189871462830251639274113 62392403597122688729455585)
    ·
      refine ⟨46794302697842016547091689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62392403597122688729455585 46794302697842016547091689)
      ·
        refine ⟨35095727023381512410318767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46794302697842016547091689 35095727023381512410318767)
        ·
          refine ⟨52643590535072268615478151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35095727023381512410318767 52643590535072268615478151)
          ·
            refine ⟨78965385802608402923217227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52643590535072268615478151 78965385802608402923217227)
            ·
              refine ⟨118448078703912604384825841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78965385802608402923217227 118448078703912604384825841)
              ·
                refine ⟨88836059027934453288619381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118448078703912604384825841 88836059027934453288619381)
                ·
                  refine ⟨8328380533868854995808067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88836059027934453288619381 8328380533868854995808067)
                  ·
                    refine ⟨12492570800803282493712101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8328380533868854995808067 12492570800803282493712101)
                    ·
                      refine ⟨2342357025150615467571019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12492570800803282493712101 2342357025150615467571019)
                      ·
                        rfl

theorem cell23_4561724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_4561724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561724 prefixEnd_4561724 := by exact prefixLift 4561724
  have htrace : WordTrace (prefixWord ++ tailWord_4561724) baseStart_4561724 baseEnd_4561724 := by
    simpa [prefixWord, tailWord_4561724, baseEnd_4561724] using wordTrace_append hprefix tailTrace_4561724
  have hstable : (prefixWord ++ tailWord_4561724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561724).length < 2 ^ (prefixWord ++ tailWord_4561724).sum := by decide
  have hdescent : baseEnd_4561724 < baseStart_4561724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561744 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 5]
def baseStart_4561744 : Nat := 118140960795 + 4561744 * 2 ^ 59
def prefixEnd_4561744 : Nat := 4983230072969 + 3 ^ 40 * 4561744 * 2
def baseEnd_4561744 : Nat := 2342367294763705389320927

theorem tailTrace_4561744 : CollatzResearch.WordTrace tailWord_4561744 prefixEnd_4561744 2342367294763705389320927 := by
  unfold tailWord_4561744
  simp only [CollatzResearch.WordTrace]
  refine ⟨83190236192794023347138143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110920314923725364462850857 83190236192794023347138143)
  ·
    refine ⟨124785354289191035020707215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83190236192794023347138143 124785354289191035020707215)
    ·
      refine ⟨187178031433786552531060823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124785354289191035020707215 187178031433786552531060823)
      ·
        refine ⟨280767047150679828796591235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187178031433786552531060823 280767047150679828796591235)
        ·
          refine ⟨421150570726019743194886853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280767047150679828796591235 421150570726019743194886853)
          ·
            refine ⟨78965732011128701849041285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 421150570726019743194886853 78965732011128701849041285)
            ·
              refine ⟨14806074752086631596695241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78965732011128701849041285 14806074752086631596695241)
              ·
                refine ⟨11104556064064973697521431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14806074752086631596695241 11104556064064973697521431)
                ·
                  refine ⟨16656834096097460546282147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11104556064064973697521431 16656834096097460546282147)
                  ·
                    refine ⟨24985251144146190819423221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16656834096097460546282147 24985251144146190819423221)
                    ·
                      refine ⟨2342367294763705389320927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24985251144146190819423221 2342367294763705389320927)
                      ·
                        rfl

theorem cell23_4561744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 5].length) (baseStart_4561744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561744 prefixEnd_4561744 := by exact prefixLift 4561744
  have htrace : WordTrace (prefixWord ++ tailWord_4561744) baseStart_4561744 baseEnd_4561744 := by
    simpa [prefixWord, tailWord_4561744, baseEnd_4561744] using wordTrace_append hprefix tailTrace_4561744
  have hstable : (prefixWord ++ tailWord_4561744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561744).length < 2 ^ (prefixWord ++ tailWord_4561744).sum := by decide
  have hdescent : baseEnd_4561744 < baseStart_4561744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561754 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6]
def baseStart_4561754 : Nat := 118140960795 + 4561754 * 2 ^ 59
def prefixEnd_4561754 : Nat := 4983230072969 + 3 ^ 40 * 4561754 * 2
def baseEnd_4561754 : Nat := 2342372429570250350195881

theorem tailTrace_4561754 : CollatzResearch.WordTrace tailWord_4561754 prefixEnd_4561754 2342372429570250350195881 := by
  unfold tailWord_4561754
  simp only [CollatzResearch.WordTrace]
  refine ⟨41595209278887954600535079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110920558077034545601426877 41595209278887954600535079)
  ·
    refine ⟨62392813918331931900802619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41595209278887954600535079 62392813918331931900802619)
    ·
      refine ⟨93589220877497897851203929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62392813918331931900802619 93589220877497897851203929)
      ·
        refine ⟨70191915658123423388402947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93589220877497897851203929 70191915658123423388402947)
        ·
          refine ⟨105287873487185135082604421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70191915658123423388402947 105287873487185135082604421)
          ·
            refine ⟨19741476278847212827988329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105287873487185135082604421 19741476278847212827988329)
            ·
              refine ⟨14806107209135409620991247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19741476278847212827988329 14806107209135409620991247)
              ·
                refine ⟨22209160813703114431486871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14806107209135409620991247 22209160813703114431486871)
                ·
                  refine ⟨33313741220554671647230307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22209160813703114431486871 33313741220554671647230307)
                  ·
                    refine ⟨49970611830832007470845461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33313741220554671647230307 49970611830832007470845461)
                    ·
                      refine ⟨2342372429570250350195881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49970611830832007470845461 2342372429570250350195881)
                      ·
                        rfl

theorem cell23_4561754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_4561754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561754 prefixEnd_4561754 := by exact prefixLift 4561754
  have htrace : WordTrace (prefixWord ++ tailWord_4561754) baseStart_4561754 baseEnd_4561754 := by
    simpa [prefixWord, tailWord_4561754, baseEnd_4561754] using wordTrace_append hprefix tailTrace_4561754
  have hstable : (prefixWord ++ tailWord_4561754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561754).length < 2 ^ (prefixWord ++ tailWord_4561754).sum := by decide
  have hdescent : baseEnd_4561754 < baseStart_4561754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561761 : List Nat := [1, 2, 3, 1, 1, 1, 2, 6, 1, 2, 3]
def baseStart_4561761 : Nat := 118140960795 + 4561761 * 2 ^ 59
def prefixEnd_4561761 : Nat := 4983230072969 + 3 ^ 40 * 4561761 * 2
def baseEnd_4561761 : Nat := 2342376023934831822808349

theorem tailTrace_4561761 : CollatzResearch.WordTrace tailWord_4561761 prefixEnd_4561761 2342376023934831822808349 := by
  unfold tailWord_4561761
  simp only [CollatzResearch.WordTrace]
  refine ⟨166381092426526458597645137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110920728284350972398430091 166381092426526458597645137)
  ·
    refine ⟨124785819319894843948233853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166381092426526458597645137 124785819319894843948233853)
    ·
      refine ⟨46794682244960566480587695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124785819319894843948233853 46794682244960566480587695)
      ·
        refine ⟨70192023367440849720881543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46794682244960566480587695 70192023367440849720881543)
        ·
          refine ⟨105288035051161274581322315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70192023367440849720881543 105288035051161274581322315)
          ·
            refine ⟨157932052576741911871983473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105288035051161274581322315 157932052576741911871983473)
            ·
              refine ⟨118449039432556433903987605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157932052576741911871983473 118449039432556433903987605)
              ·
                refine ⟨5552298723401082839249419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118449039432556433903987605 5552298723401082839249419)
                ·
                  refine ⟨8328448085101624258874129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5552298723401082839249419 8328448085101624258874129)
                  ·
                    refine ⟨6246336063826218194155597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8328448085101624258874129 6246336063826218194155597)
                    ·
                      refine ⟨2342376023934831822808349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6246336063826218194155597 2342376023934831822808349)
                      ·
                        rfl

theorem cell23_4561761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_4561761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561761 prefixEnd_4561761 := by exact prefixLift 4561761
  have htrace : WordTrace (prefixWord ++ tailWord_4561761) baseStart_4561761 baseEnd_4561761 := by
    simpa [prefixWord, tailWord_4561761, baseEnd_4561761] using wordTrace_append hprefix tailTrace_4561761
  have hstable : (prefixWord ++ tailWord_4561761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561761).length < 2 ^ (prefixWord ++ tailWord_4561761).sum := by decide
  have hdescent : baseEnd_4561761 < baseStart_4561761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561764 : List Nat := [2, 3, 1, 1, 4, 1, 2, 9]
def baseStart_4561764 : Nat := 118140960795 + 4561764 * 2 ^ 59
def prefixEnd_4561764 : Nat := 4983230072969 + 3 ^ 40 * 4561764 * 2
def baseEnd_4561764 : Nat := 86754724606547974484105

theorem tailTrace_4561764 : CollatzResearch.WordTrace tailWord_4561764 prefixEnd_4561764 86754724606547974484105 := by
  unfold tailWord_4561764
  simp only [CollatzResearch.WordTrace]
  refine ⟨83190600922757795055002173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110920801230343726740002897 83190600922757795055002173)
  ·
    refine ⟨31196475346034173145625815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83190600922757795055002173 31196475346034173145625815)
    ·
      refine ⟨46794713019051259718438723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31196475346034173145625815 46794713019051259718438723)
      ·
        refine ⟨70192069528576889577658085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46794713019051259718438723 70192069528576889577658085)
        ·
          refine ⟨13161013036608166795810891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70192069528576889577658085 13161013036608166795810891)
          ·
            refine ⟨19741519554912250193716337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13161013036608166795810891 19741519554912250193716337)
            ·
              refine ⟨14806139666184187645287253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19741519554912250193716337 14806139666184187645287253)
              ·
                refine ⟨86754724606547974484105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14806139666184187645287253 86754724606547974484105)
                ·
                  rfl

theorem cell23_4561764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 9].length) (baseStart_4561764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561764 prefixEnd_4561764 := by exact prefixLift 4561764
  have htrace : WordTrace (prefixWord ++ tailWord_4561764) baseStart_4561764 baseEnd_4561764 := by
    simpa [prefixWord, tailWord_4561764, baseEnd_4561764] using wordTrace_append hprefix tailTrace_4561764
  have hstable : (prefixWord ++ tailWord_4561764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561764).length < 2 ^ (prefixWord ++ tailWord_4561764).sum := by decide
  have hdescent : baseEnd_4561764 < baseStart_4561764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561791 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 4, 1, 3]
def baseStart_4561791 : Nat := 118140960795 + 4561791 * 2 ^ 59
def prefixEnd_4561791 : Nat := 4983230072969 + 3 ^ 40 * 4561791 * 2
def baseEnd_4561791 : Nat := 2342391428354466705433211

theorem tailTrace_4561791 : CollatzResearch.WordTrace tailWord_4561791 prefixEnd_4561791 2342391428354466705433211 := by
  unfold tailWord_4561791
  simp only [CollatzResearch.WordTrace]
  refine ⟨166382186616417773721237227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110921457744278515814158151 166382186616417773721237227)
  ·
    refine ⟨249573279924626660581855841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166382186616417773721237227 249573279924626660581855841)
    ·
      refine ⟨187179959943469995436391881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249573279924626660581855841 187179959943469995436391881)
      ·
        refine ⟨140384969957602496577293911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187179959943469995436391881 140384969957602496577293911)
        ·
          refine ⟨210577454936403744865940867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140384969957602496577293911 210577454936403744865940867)
          ·
            refine ⟨315866182404605617298911301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210577454936403744865940867 315866182404605617298911301)
            ·
              refine ⟨59224909200863553243545869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 315866182404605617298911301 59224909200863553243545869)
              ·
                refine ⟨22209340950323832466329701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59224909200863553243545869 22209340950323832466329701)
                ·
                  refine ⟨4164251428185718587436819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22209340950323832466329701 4164251428185718587436819)
                  ·
                    refine ⟨6246377142278577881155229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4164251428185718587436819 6246377142278577881155229)
                    ·
                      refine ⟨2342391428354466705433211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6246377142278577881155229 2342391428354466705433211)
                      ·
                        rfl

theorem cell23_4561791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 1, 3].length) (baseStart_4561791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561791 prefixEnd_4561791 := by exact prefixLift 4561791
  have htrace : WordTrace (prefixWord ++ tailWord_4561791) baseStart_4561791 baseEnd_4561791 := by
    simpa [prefixWord, tailWord_4561791, baseEnd_4561791] using wordTrace_append hprefix tailTrace_4561791
  have hstable : (prefixWord ++ tailWord_4561791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561791).length < 2 ^ (prefixWord ++ tailWord_4561791).sum := by decide
  have hdescent : baseEnd_4561791 < baseStart_4561791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561905 : List Nat := [1, 2, 2, 2, 4, 2, 3, 2, 5]
def baseStart_4561905 : Nat := 118140960795 + 4561905 * 2 ^ 59
def prefixEnd_4561905 : Nat := 4983230072969 + 3 ^ 40 * 4561905 * 2
def baseEnd_4561905 : Nat := 260272218349897695489743

theorem tailTrace_4561905 : CollatzResearch.WordTrace tailWord_4561905 prefixEnd_4561905 260272218349897695489743 := by
  unfold tailWord_4561905
  simp only [CollatzResearch.WordTrace]
  refine ⟨166386344538004771190887169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110924229692003180793924779 166386344538004771190887169)
  ·
    refine ⟨124789758403503578393165377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166386344538004771190887169 124789758403503578393165377)
    ·
      refine ⟨93592318802627683794874033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124789758403503578393165377 93592318802627683794874033)
      ·
        refine ⟨70194239101970762846155525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93592318802627683794874033 70194239101970762846155525)
        ·
          refine ⟨13161419831619518033654161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70194239101970762846155525 13161419831619518033654161)
          ·
            refine ⟨9871064873714638525240621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13161419831619518033654161 9871064873714638525240621)
            ·
              refine ⟨3701649327642989446965233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9871064873714638525240621 3701649327642989446965233)
              ·
                refine ⟨2776236995732242085223925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3701649327642989446965233 2776236995732242085223925)
                ·
                  refine ⟨260272218349897695489743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2776236995732242085223925 260272218349897695489743)
                  ·
                    rfl

theorem cell23_4561905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 5].length) (baseStart_4561905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561905 prefixEnd_4561905 := by exact prefixLift 4561905
  have htrace : WordTrace (prefixWord ++ tailWord_4561905) baseStart_4561905 baseEnd_4561905 := by
    simpa [prefixWord, tailWord_4561905, baseEnd_4561905] using wordTrace_append hprefix tailTrace_4561905
  have hstable : (prefixWord ++ tailWord_4561905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561905).length < 2 ^ (prefixWord ++ tailWord_4561905).sum := by decide
  have hdescent : baseEnd_4561905 < baseStart_4561905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561971 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 3]
def baseStart_4561971 : Nat := 118140960795 + 4561971 * 2 ^ 59
def prefixEnd_4561971 : Nat := 4983230072969 + 3 ^ 40 * 4561971 * 2
def baseEnd_4561971 : Nat := 2342483854872276001182383

theorem tailTrace_4561971 : CollatzResearch.WordTrace tailWord_4561971 prefixEnd_4561971 2342483854872276001182383 := by
  unfold tailWord_4561971
  simp only [CollatzResearch.WordTrace]
  refine ⟨166388751755765664462789767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110925834503843776308526511 166388751755765664462789767)
  ·
    refine ⟨249583127633648496694184651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166388751755765664462789767 249583127633648496694184651)
    ·
      refine ⟨374374691450472745041276977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249583127633648496694184651 374374691450472745041276977)
      ·
        refine ⟨280781018587854558780957733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374374691450472745041276977 280781018587854558780957733)
        ·
          refine ⟨52646440985222729771429575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 280781018587854558780957733 52646440985222729771429575)
          ·
            refine ⟨78969661477834094657144363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52646440985222729771429575 78969661477834094657144363)
            ·
              refine ⟨118454492216751141985716545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78969661477834094657144363 118454492216751141985716545)
              ·
                refine ⟨88840869162563356489287409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118454492216751141985716545 88840869162563356489287409)
                ·
                  refine ⟨66630651871922517366965557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88840869162563356489287409 66630651871922517366965557)
                  ·
                    refine ⟨6246623612992736003153021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66630651871922517366965557 6246623612992736003153021)
                    ·
                      refine ⟨2342483854872276001182383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6246623612992736003153021 2342483854872276001182383)
                      ·
                        rfl

theorem cell23_4561971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 3].length) (baseStart_4561971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561971 prefixEnd_4561971 := by exact prefixLift 4561971
  have htrace : WordTrace (prefixWord ++ tailWord_4561971) baseStart_4561971 baseEnd_4561971 := by
    simpa [prefixWord, tailWord_4561971, baseEnd_4561971] using wordTrace_append hprefix tailTrace_4561971
  have hstable : (prefixWord ++ tailWord_4561971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561971).length < 2 ^ (prefixWord ++ tailWord_4561971).sum := by decide
  have hdescent : baseEnd_4561971 < baseStart_4561971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4561972 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_4561972 : Nat := 118140960795 + 4561972 * 2 ^ 59
def prefixEnd_4561972 : Nat := 4983230072969 + 3 ^ 40 * 4561972 * 2
def baseEnd_4561972 : Nat := 2342484368352930497269879

theorem tailTrace_4561972 : CollatzResearch.WordTrace tailWord_4561972 prefixEnd_4561972 2342484368352930497269879 := by
  unfold tailWord_4561972
  simp only [CollatzResearch.WordTrace]
  refine ⟨83194394114381020816788085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110925858819174694422384113 83194394114381020816788085)
  ·
    refine ⟨7799474448223220701573883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83194394114381020816788085 7799474448223220701573883)
    ·
      refine ⟨11699211672334831052360825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7799474448223220701573883 11699211672334831052360825)
      ·
        refine ⟨8774408754251123289270619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11699211672334831052360825 8774408754251123289270619)
        ·
          refine ⟨13161613131376684933905929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8774408754251123289270619 13161613131376684933905929)
          ·
            refine ⟨9871209848532513700429447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13161613131376684933905929 9871209848532513700429447)
            ·
              refine ⟨14806814772798770550644171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9871209848532513700429447 14806814772798770550644171)
              ·
                refine ⟨22210222159198155825966257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14806814772798770550644171 22210222159198155825966257)
                ·
                  refine ⟨16657666619398616869474693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22210222159198155825966257 16657666619398616869474693)
                  ·
                    refine ⟨3123312491137240663026505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16657666619398616869474693 3123312491137240663026505)
                    ·
                      refine ⟨2342484368352930497269879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3123312491137240663026505 2342484368352930497269879)
                      ·
                        rfl

theorem cell23_4561972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_4561972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4561972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4561972 prefixEnd_4561972 := by exact prefixLift 4561972
  have htrace : WordTrace (prefixWord ++ tailWord_4561972) baseStart_4561972 baseEnd_4561972 := by
    simpa [prefixWord, tailWord_4561972, baseEnd_4561972] using wordTrace_append hprefix tailTrace_4561972
  have hstable : (prefixWord ++ tailWord_4561972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4561972).length < 2 ^ (prefixWord ++ tailWord_4561972).sum := by decide
  have hdescent : baseEnd_4561972 < baseStart_4561972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4561972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562008 : List Nat := [2, 1, 2, 2, 1, 3, 3, 3, 1, 5]
def baseStart_4562008 : Nat := 118140960795 + 4562008 * 2 ^ 59
def prefixEnd_4562008 : Nat := 4983230072969 + 3 ^ 40 * 4562008 * 2
def baseEnd_4562008 : Nat := 780834284552164118806571

theorem tailTrace_4562008 : CollatzResearch.WordTrace tailWord_4562008 prefixEnd_4562008 780834284552164118806571 := by
  unfold tailWord_4562008
  simp only [CollatzResearch.WordTrace]
  refine ⟨83195050628315809890943339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110926734171087746521257785 83195050628315809890943339)
  ·
    refine ⟨124792575942473714836415009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83195050628315809890943339 124792575942473714836415009)
    ·
      refine ⟨93594431956855286127311257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124792575942473714836415009 93594431956855286127311257)
      ·
        refine ⟨70195823967641464595483443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93594431956855286127311257 70195823967641464595483443)
        ·
          refine ⟨105293735951462196893225165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70195823967641464595483443 105293735951462196893225165)
          ·
            refine ⟨39485150981798323834959437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105293735951462196893225165 39485150981798323834959437)
            ·
              refine ⟨14806931618174371438109789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39485150981798323834959437 14806931618174371438109789)
              ·
                refine ⟨5552599356815389289291171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14806931618174371438109789 5552599356815389289291171)
                ·
                  refine ⟨8328899035223083933936757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5552599356815389289291171 8328899035223083933936757)
                  ·
                    refine ⟨780834284552164118806571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8328899035223083933936757 780834284552164118806571)
                    ·
                      rfl

theorem cell23_4562008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_4562008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562008 prefixEnd_4562008 := by exact prefixLift 4562008
  have htrace : WordTrace (prefixWord ++ tailWord_4562008) baseStart_4562008 baseEnd_4562008 := by
    simpa [prefixWord, tailWord_4562008, baseEnd_4562008] using wordTrace_append hprefix tailTrace_4562008
  have hstable : (prefixWord ++ tailWord_4562008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562008).length < 2 ^ (prefixWord ++ tailWord_4562008).sum := by decide
  have hdescent : baseEnd_4562008 < baseStart_4562008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562045 : List Nat := [1, 4, 1, 1, 3, 1, 4, 2, 1, 1, 4]
def baseStart_4562045 : Nat := 118140960795 + 4562045 * 2 ^ 59
def prefixEnd_4562045 : Nat := 4983230072969 + 3 ^ 40 * 4562045 * 2
def baseEnd_4562045 : Nat := 2342521852440708711657043

theorem tailTrace_4562045 : CollatzResearch.WordTrace tailWord_4562045 prefixEnd_4562045 2342521852440708711657043 := by
  unfold tailWord_4562045
  simp only [CollatzResearch.WordTrace]
  refine ⟨166391450757497575100983589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110927633838331716733989059 166391450757497575100983589)
  ·
    refine ⟨31198397017030795331434423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166391450757497575100983589 31198397017030795331434423)
    ·
      refine ⟨46797595525546192997151635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31198397017030795331434423 46797595525546192997151635)
      ·
        refine ⟨70196393288319289495727453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46797595525546192997151635 70196393288319289495727453)
        ·
          refine ⟨26323647483119733560897795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70196393288319289495727453 26323647483119733560897795)
          ·
            refine ⟨39485471224679600341346693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26323647483119733560897795 39485471224679600341346693)
            ·
              refine ⟨7403525854627425064002505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39485471224679600341346693 7403525854627425064002505)
              ·
                refine ⟨5552644390970568798001879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7403525854627425064002505 5552644390970568798001879)
                ·
                  refine ⟨8328966586455853197002819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5552644390970568798001879 8328966586455853197002819)
                  ·
                    refine ⟨12493449879683779795504229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8328966586455853197002819 12493449879683779795504229)
                    ·
                      refine ⟨2342521852440708711657043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12493449879683779795504229 2342521852440708711657043)
                      ·
                        rfl

theorem cell23_4562045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_4562045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562045 prefixEnd_4562045 := by exact prefixLift 4562045
  have htrace : WordTrace (prefixWord ++ tailWord_4562045) baseStart_4562045 baseEnd_4562045 := by
    simpa [prefixWord, tailWord_4562045, baseEnd_4562045] using wordTrace_append hprefix tailTrace_4562045
  have hstable : (prefixWord ++ tailWord_4562045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562045).length < 2 ^ (prefixWord ++ tailWord_4562045).sum := by decide
  have hdescent : baseEnd_4562045 < baseStart_4562045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562048 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 3]
def baseStart_4562048 : Nat := 118140960795 + 4562048 * 2 ^ 59
def prefixEnd_4562048 : Nat := 4983230072969 + 3 ^ 40 * 4562048 * 2
def baseEnd_4562048 : Nat := 2342523392882672199919529

theorem tailTrace_4562048 : CollatzResearch.WordTrace tailWord_4562048 prefixEnd_4562048 2342523392882672199919529 := by
  unfold tailWord_4562048
  simp only [CollatzResearch.WordTrace]
  refine ⟨83195780088243353306671399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110927706784324471075561865 83195780088243353306671399)
  ·
    refine ⟨124793670132365029960007099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83195780088243353306671399 124793670132365029960007099)
    ·
      refine ⟨187190505198547544940010649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124793670132365029960007099 187190505198547544940010649)
      ·
        refine ⟨140392878898910658705007987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187190505198547544940010649 140392878898910658705007987)
        ·
          refine ⟨210589318348365988057511981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140392878898910658705007987 210589318348365988057511981)
          ·
            refine ⟨78970994380637245521566993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210589318348365988057511981 78970994380637245521566993)
            ·
              refine ⟨59228245785477934141175245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78970994380637245521566993 59228245785477934141175245)
              ·
                refine ⟨22210592169554225302940717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59228245785477934141175245 22210592169554225302940717)
                ·
                  refine ⟨8328972063582834488602769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22210592169554225302940717 8328972063582834488602769)
                  ·
                    refine ⟨6246729047687125866452077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8328972063582834488602769 6246729047687125866452077)
                    ·
                      refine ⟨2342523392882672199919529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6246729047687125866452077 2342523392882672199919529)
                      ·
                        rfl

theorem cell23_4562048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_4562048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562048 prefixEnd_4562048 := by exact prefixLift 4562048
  have htrace : WordTrace (prefixWord ++ tailWord_4562048) baseStart_4562048 baseEnd_4562048 := by
    simpa [prefixWord, tailWord_4562048, baseEnd_4562048] using wordTrace_append hprefix tailTrace_4562048
  have hstable : (prefixWord ++ tailWord_4562048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562048).length < 2 ^ (prefixWord ++ tailWord_4562048).sum := by decide
  have hdescent : baseEnd_4562048 < baseStart_4562048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562051 : List Nat := [1, 1, 1, 3, 3, 2, 3, 9]
def baseStart_4562051 : Nat := 118140960795 + 4562051 * 2 ^ 59
def prefixEnd_4562051 : Nat := 4983230072969 + 3 ^ 40 * 4562051 * 2
def baseEnd_4562051 : Nat := 86760182715727247710445

theorem tailTrace_4562051 : CollatzResearch.WordTrace tailWord_4562051 prefixEnd_4562051 86760182715727247710445 := by
  unfold tailWord_4562051
  simp only [CollatzResearch.WordTrace]
  refine ⟨166391669595475838125702007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110927779730317225417134671 166391669595475838125702007)
  ·
    refine ⟨249587504393213757188553011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166391669595475838125702007 249587504393213757188553011)
    ·
      refine ⟨374381256589820635782829517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249587504393213757188553011 374381256589820635782829517)
      ·
        refine ⟨140392971221182738418561069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 374381256589820635782829517 140392971221182738418561069)
        ·
          refine ⟨52647364207943526906960401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140392971221182738418561069 52647364207943526906960401)
          ·
            refine ⟨39485523155957645180220301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52647364207943526906960401 39485523155957645180220301)
            ·
              refine ⟨14807071183484116942582613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39485523155957645180220301 14807071183484116942582613)
              ·
                refine ⟨86760182715727247710445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14807071183484116942582613 86760182715727247710445)
                ·
                  rfl

theorem cell23_4562051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 9].length) (baseStart_4562051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562051 prefixEnd_4562051 := by exact prefixLift 4562051
  have htrace : WordTrace (prefixWord ++ tailWord_4562051) baseStart_4562051 baseEnd_4562051 := by
    simpa [prefixWord, tailWord_4562051, baseEnd_4562051] using wordTrace_append hprefix tailTrace_4562051
  have hstable : (prefixWord ++ tailWord_4562051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562051).length < 2 ^ (prefixWord ++ tailWord_4562051).sum := by decide
  have hdescent : baseEnd_4562051 < baseStart_4562051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562056 : List Nat := [2, 1, 3, 4, 2, 2, 1, 3, 1, 1, 3]
def baseStart_4562056 : Nat := 118140960795 + 4562056 * 2 ^ 59
def prefixEnd_4562056 : Nat := 4983230072969 + 3 ^ 40 * 4562056 * 2
def baseEnd_4562056 : Nat := 2342527500727908168619493

theorem tailTrace_4562056 : CollatzResearch.WordTrace tailWord_4562056 prefixEnd_4562056 2342527500727908168619493 := by
  unfold tailWord_4562056
  simp only [CollatzResearch.WordTrace]
  refine ⟨83195925980228861989817011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110927901306971815986422681 83195925980228861989817011)
  ·
    refine ⟨124793888970343292984725517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83195925980228861989817011 124793888970343292984725517)
    ·
      refine ⟨46797708363878734869272069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124793888970343292984725517 46797708363878734869272069)
      ·
        refine ⟨8774570318227262787988513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46797708363878734869272069 8774570318227262787988513)
        ·
          refine ⟨6580927738670447090991385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8774570318227262787988513 6580927738670447090991385)
          ·
            refine ⟨4935695804002835318243539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6580927738670447090991385 4935695804002835318243539)
            ·
              refine ⟨7403543706004252977365309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4935695804002835318243539 7403543706004252977365309)
              ·
                refine ⟨2776328889751594866511991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7403543706004252977365309 2776328889751594866511991)
                ·
                  refine ⟨4164493334627392299767987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2776328889751594866511991 4164493334627392299767987)
                  ·
                    refine ⟨6246740001941088449651981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4164493334627392299767987 6246740001941088449651981)
                    ·
                      refine ⟨2342527500727908168619493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6246740001941088449651981 2342527500727908168619493)
                      ·
                        rfl

theorem cell23_4562056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_4562056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562056 prefixEnd_4562056 := by exact prefixLift 4562056
  have htrace : WordTrace (prefixWord ++ tailWord_4562056) baseStart_4562056 baseEnd_4562056 := by
    simpa [prefixWord, tailWord_4562056, baseEnd_4562056] using wordTrace_append hprefix tailTrace_4562056
  have hstable : (prefixWord ++ tailWord_4562056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562056).length < 2 ^ (prefixWord ++ tailWord_4562056).sum := by decide
  have hdescent : baseEnd_4562056 < baseStart_4562056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562058 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_4562058 : Nat := 118140960795 + 4562058 * 2 ^ 59
def prefixEnd_4562058 : Nat := 4983230072969 + 3 ^ 40 * 4562058 * 2
def baseEnd_4562058 : Nat := 2342528527689217160794483

theorem tailTrace_4562058 : CollatzResearch.WordTrace tailWord_4562058 prefixEnd_4562058 2342528527689217160794483 := by
  unfold tailWord_4562058
  simp only [CollatzResearch.WordTrace]
  refine ⟨41597981226612619580301707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110927949937633652214137885 41597981226612619580301707)
  ·
    refine ⟨62396971839918929370452561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41597981226612619580301707 62396971839918929370452561)
    ·
      refine ⟨46797728879939197027839421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62396971839918929370452561 46797728879939197027839421)
      ·
        refine ⟨17549148329977198885439783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46797728879939197027839421 17549148329977198885439783)
        ·
          refine ⟨26323722494965798328159675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17549148329977198885439783 26323722494965798328159675)
          ·
            refine ⟨39485583742448697492239513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26323722494965798328159675 39485583742448697492239513)
            ·
              refine ⟨29614187806836523119179635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39485583742448697492239513 29614187806836523119179635)
              ·
                refine ⟨44421281710254784678769453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29614187806836523119179635 44421281710254784678769453)
                ·
                  refine ⟨16657980641345544254538545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44421281710254784678769453 16657980641345544254538545)
                  ·
                    refine ⟨12493485481009158190903909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16657980641345544254538545 12493485481009158190903909)
                    ·
                      refine ⟨2342528527689217160794483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12493485481009158190903909 2342528527689217160794483)
                      ·
                        rfl

theorem cell23_4562058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_4562058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562058 prefixEnd_4562058 := by exact prefixLift 4562058
  have htrace : WordTrace (prefixWord ++ tailWord_4562058) baseStart_4562058 baseEnd_4562058 := by
    simpa [prefixWord, tailWord_4562058, baseEnd_4562058] using wordTrace_append hprefix tailTrace_4562058
  have hstable : (prefixWord ++ tailWord_4562058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562058).length < 2 ^ (prefixWord ++ tailWord_4562058).sum := by decide
  have hdescent : baseEnd_4562058 < baseStart_4562058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562148 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_4562148 : Nat := 118140960795 + 4562148 * 2 ^ 59
def prefixEnd_4562148 : Nat := 4983230072969 + 3 ^ 40 * 4562148 * 2
def baseEnd_4562148 : Nat := 2342574740948121808669069

theorem tailTrace_4562148 : CollatzResearch.WordTrace tailWord_4562148 prefixEnd_4562148 2342574740948121808669069 := by
  unfold tailWord_4562148
  simp only [CollatzResearch.WordTrace]
  refine ⟨83197603738062211845991549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110930138317416282461322065 83197603738062211845991549)
  ·
    refine ⟨31199101401773329442246831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83197603738062211845991549 31199101401773329442246831)
    ·
      refine ⟨46798652102659994163370247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31199101401773329442246831 46798652102659994163370247)
      ·
        refine ⟨70197978153989991245055371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46798652102659994163370247 70197978153989991245055371)
        ·
          refine ⟨105296967230984986867583057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70197978153989991245055371 105296967230984986867583057)
          ·
            refine ⟨78972725423238740150687293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105296967230984986867583057 78972725423238740150687293)
            ·
              refine ⟨29614772033714527556507735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78972725423238740150687293 29614772033714527556507735)
              ·
                refine ⟨44422158050571791334761603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29614772033714527556507735 44422158050571791334761603)
                ·
                  refine ⟨66633237075857687002142405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44422158050571791334761603 66633237075857687002142405)
                  ·
                    refine ⟨12493731951723316312901701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66633237075857687002142405 12493731951723316312901701)
                    ·
                      refine ⟨2342574740948121808669069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12493731951723316312901701 2342574740948121808669069)
                      ·
                        rfl

theorem cell23_4562148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_4562148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562148 prefixEnd_4562148 := by exact prefixLift 4562148
  have htrace : WordTrace (prefixWord ++ tailWord_4562148) baseStart_4562148 baseEnd_4562148 := by
    simpa [prefixWord, tailWord_4562148, baseEnd_4562148] using wordTrace_append hprefix tailTrace_4562148
  have hstable : (prefixWord ++ tailWord_4562148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562148).length < 2 ^ (prefixWord ++ tailWord_4562148).sum := by decide
  have hdescent : baseEnd_4562148 < baseStart_4562148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562152 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 1, 4, 2]
def baseStart_4562152 : Nat := 118140960795 + 4562152 * 2 ^ 59
def prefixEnd_4562152 : Nat := 4983230072969 + 3 ^ 40 * 4562152 * 2
def baseEnd_4562152 : Nat := 2342576794870739793019051

theorem tailTrace_4562152 : CollatzResearch.WordTrace tailWord_4562152 prefixEnd_4562152 2342576794870739793019051 := by
  unfold tailWord_4562152
  simp only [CollatzResearch.WordTrace]
  refine ⟨83197676684054966187564355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110930235578739954916752473 83197676684054966187564355)
  ·
    refine ⟨124796515026082449281346533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83197676684054966187564355 124796515026082449281346533)
    ·
      refine ⟨23399346567390459240252475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124796515026082449281346533 23399346567390459240252475)
      ·
        refine ⟨35099019851085688860378713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23399346567390459240252475 35099019851085688860378713)
        ·
          refine ⟨26324264888314266645284035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35099019851085688860378713 26324264888314266645284035)
          ·
            refine ⟨39486397332471399967926053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26324264888314266645284035 39486397332471399967926053)
            ·
              refine ⟨7403699499838387493986135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39486397332471399967926053 7403699499838387493986135)
              ·
                refine ⟨11105549249757581240979203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7403699499838387493986135 11105549249757581240979203)
                ·
                  refine ⟨16658323874636371861468805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11105549249757581240979203 16658323874636371861468805)
                  ·
                    refine ⟨3123435726494319724025401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16658323874636371861468805 3123435726494319724025401)
                    ·
                      refine ⟨2342576794870739793019051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3123435726494319724025401 2342576794870739793019051)
                      ·
                        rfl

theorem cell23_4562152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_4562152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562152 prefixEnd_4562152 := by exact prefixLift 4562152
  have htrace : WordTrace (prefixWord ++ tailWord_4562152) baseStart_4562152 baseEnd_4562152 := by
    simpa [prefixWord, tailWord_4562152, baseEnd_4562152] using wordTrace_append hprefix tailTrace_4562152
  have hstable : (prefixWord ++ tailWord_4562152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562152).length < 2 ^ (prefixWord ++ tailWord_4562152).sum := by decide
  have hdescent : baseEnd_4562152 < baseStart_4562152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562158 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 9]
def baseStart_4562158 : Nat := 118140960795 + 4562158 * 2 ^ 59
def prefixEnd_4562158 : Nat := 4983230072969 + 3 ^ 40 * 4562158 * 2
def baseEnd_4562158 : Nat := 260286652861629641060447

theorem tailTrace_4562158 : CollatzResearch.WordTrace tailWord_4562158 prefixEnd_4562158 260286652861629641060447 := by
  unfold tailWord_4562158
  simp only [CollatzResearch.WordTrace]
  refine ⟨20799446525761024424980891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110930381470725463599898085 20799446525761024424980891)
  ·
    refine ⟨31199169788641536637471337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20799446525761024424980891 31199169788641536637471337)
    ·
      refine ⟨23399377341481152478103503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31199169788641536637471337 23399377341481152478103503)
      ·
        refine ⟨35099066012221728717155255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23399377341481152478103503 35099066012221728717155255)
        ·
          refine ⟨52648599018332593075732883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35099066012221728717155255 52648599018332593075732883)
          ·
            refine ⟨78972898527498889613599325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52648599018332593075732883 78972898527498889613599325)
            ·
              refine ⟨29614836947812083605099747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78972898527498889613599325 29614836947812083605099747)
              ·
                refine ⟨44422255421718125407649621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29614836947812083605099747 44422255421718125407649621)
                ·
                  refine ⟨260286652861629641060447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44422255421718125407649621 260286652861629641060447)
                  ·
                    rfl

theorem cell23_4562158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_4562158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562158 prefixEnd_4562158 := by exact prefixLift 4562158
  have htrace : WordTrace (prefixWord ++ tailWord_4562158) baseStart_4562158 baseEnd_4562158 := by
    simpa [prefixWord, tailWord_4562158, baseEnd_4562158] using wordTrace_append hprefix tailTrace_4562158
  have hstable : (prefixWord ++ tailWord_4562158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562158).length < 2 ^ (prefixWord ++ tailWord_4562158).sum := by decide
  have hdescent : baseEnd_4562158 < baseStart_4562158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562175 : List Nat := [1, 1, 2, 2, 1, 5, 1, 5, 5]
def baseStart_4562175 : Nat := 118140960795 + 4562175 * 2 ^ 59
def prefixEnd_4562175 : Nat := 4983230072969 + 3 ^ 40 * 4562175 * 2
def baseEnd_4562175 : Nat := 260287622769532578114605

theorem tailTrace_4562175 : CollatzResearch.WordTrace tailWord_4562175 prefixEnd_4562175 260287622769532578114605 := by
  unfold tailWord_4562175
  simp only [CollatzResearch.WordTrace]
  refine ⟨166396192247026607303215979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110930794831351071535477319 166396192247026607303215979)
  ·
    refine ⟨249594288370539910954823969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166396192247026607303215979 249594288370539910954823969)
    ·
      refine ⟨187195716277904933216117977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249594288370539910954823969 187195716277904933216117977)
      ·
        refine ⟨140396787208428699912088483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187195716277904933216117977 140396787208428699912088483)
        ·
          refine ⟨210595180812643049868132725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140396787208428699912088483 210595180812643049868132725)
          ·
            refine ⟨19743298201185285925137443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 210595180812643049868132725 19743298201185285925137443)
            ·
              refine ⟨29614947301777928887706165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19743298201185285925137443 29614947301777928887706165)
              ·
                refine ⟨2776401309541680833222453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29614947301777928887706165 2776401309541680833222453)
                ·
                  refine ⟨260287622769532578114605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2776401309541680833222453 260287622769532578114605)
                  ·
                    rfl

theorem cell23_4562175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 5].length) (baseStart_4562175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562175 prefixEnd_4562175 := by exact prefixLift 4562175
  have htrace : WordTrace (prefixWord ++ tailWord_4562175) baseStart_4562175 baseEnd_4562175 := by
    simpa [prefixWord, tailWord_4562175, baseEnd_4562175] using wordTrace_append hprefix tailTrace_4562175
  have hstable : (prefixWord ++ tailWord_4562175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562175).length < 2 ^ (prefixWord ++ tailWord_4562175).sum := by decide
  have hdescent : baseEnd_4562175 < baseStart_4562175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562205 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 1, 7]
def baseStart_4562205 : Nat := 118140960795 + 4562205 * 2 ^ 59
def prefixEnd_4562205 : Nat := 4983230072969 + 3 ^ 40 * 4562205 * 2
def baseEnd_4562205 : Nat := 780868003115142695218769

theorem tailTrace_4562205 : CollatzResearch.WordTrace tailWord_4562205 prefixEnd_4562205 780868003115142695218769 := by
  unfold tailWord_4562205
  simp only [CollatzResearch.WordTrace]
  refine ⟨166397286436917922426808069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110931524291278614951205379 166397286436917922426808069)
  ·
    refine ⟨31199491206922110455026513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166397286436917922426808069 31199491206922110455026513)
    ·
      refine ⟨23399618405191582841269885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31199491206922110455026513 23399618405191582841269885)
      ·
        refine ⟨8774856901946843565476207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23399618405191582841269885 8774856901946843565476207)
        ·
          refine ⟨13162285352920265348214311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8774856901946843565476207 13162285352920265348214311)
          ·
            refine ⟨19743428029380398022321467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13162285352920265348214311 19743428029380398022321467)
            ·
              refine ⟨29615142044070597033482201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19743428029380398022321467 29615142044070597033482201)
              ·
                refine ⟨22211356533052947775111651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29615142044070597033482201 22211356533052947775111651)
                ·
                  refine ⟨33317034799579421662667477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22211356533052947775111651 33317034799579421662667477)
                  ·
                    refine ⟨780868003115142695218769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33317034799579421662667477 780868003115142695218769)
                    ·
                      rfl

theorem cell23_4562205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_4562205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562205 prefixEnd_4562205 := by exact prefixLift 4562205
  have htrace : WordTrace (prefixWord ++ tailWord_4562205) baseStart_4562205 baseEnd_4562205 := by
    simpa [prefixWord, tailWord_4562205, baseEnd_4562205] using wordTrace_append hprefix tailTrace_4562205
  have hstable : (prefixWord ++ tailWord_4562205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562205).length < 2 ^ (prefixWord ++ tailWord_4562205).sum := by decide
  have hdescent : baseEnd_4562205 < baseStart_4562205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562225 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 1, 3, 4]
def baseStart_4562225 : Nat := 118140960795 + 4562225 * 2 ^ 59
def prefixEnd_4562225 : Nat := 4983230072969 + 3 ^ 40 * 4562225 * 2
def baseEnd_4562225 : Nat := 2342614278958518007406215

theorem tailTrace_4562225 : CollatzResearch.WordTrace tailWord_4562225 prefixEnd_4562225 2342614278958518007406215 := by
  unfold tailWord_4562225
  simp only [CollatzResearch.WordTrace]
  refine ⟨166398015896845465842536129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110932010597896977228357419 166398015896845465842536129)
  ·
    refine ⟨124798511922634099381902097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166398015896845465842536129 124798511922634099381902097)
    ·
      refine ⟨93598883941975574536426573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124798511922634099381902097 93598883941975574536426573)
      ·
        refine ⟨35099581478240840451159965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93598883941975574536426573 35099581478240840451159965)
        ·
          refine ⟨13162343054340315169184987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35099581478240840451159965 13162343054340315169184987)
          ·
            refine ⟨19743514581510472753777481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13162343054340315169184987 19743514581510472753777481)
            ·
              refine ⟨14807635936132854565333111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19743514581510472753777481 14807635936132854565333111)
              ·
                refine ⟨22211453904199281847999667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14807635936132854565333111 22211453904199281847999667)
                ·
                  refine ⟨33317180856298922771999501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22211453904199281847999667 33317180856298922771999501)
                  ·
                    refine ⟨12493942821112096039499813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33317180856298922771999501 12493942821112096039499813)
                    ·
                      refine ⟨2342614278958518007406215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12493942821112096039499813 2342614278958518007406215)
                      ·
                        rfl

theorem cell23_4562225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_4562225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562225 prefixEnd_4562225 := by exact prefixLift 4562225
  have htrace : WordTrace (prefixWord ++ tailWord_4562225) baseStart_4562225 baseEnd_4562225 := by
    simpa [prefixWord, tailWord_4562225, baseEnd_4562225] using wordTrace_append hprefix tailTrace_4562225
  have hstable : (prefixWord ++ tailWord_4562225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562225).length < 2 ^ (prefixWord ++ tailWord_4562225).sum := by decide
  have hdescent : baseEnd_4562225 < baseStart_4562225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562252 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 3, 4]
def baseStart_4562252 : Nat := 118140960795 + 4562252 * 2 ^ 59
def prefixEnd_4562252 : Nat := 4983230072969 + 3 ^ 40 * 4562252 * 2
def baseEnd_4562252 : Nat := 780876047645396467256197

theorem tailTrace_4562252 : CollatzResearch.WordTrace tailWord_4562252 prefixEnd_4562252 780876047645396467256197 := by
  unfold tailWord_4562252
  simp only [CollatzResearch.WordTrace]
  refine ⟨83199500333873824726884505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110932667111831766302512673 83199500333873824726884505)
  ·
    refine ⟨62399625250405368545163379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83199500333873824726884505 62399625250405368545163379)
    ·
      refine ⟨93599437875608052817745069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62399625250405368545163379 93599437875608052817745069)
      ·
        refine ⟨35099789203353019806654401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93599437875608052817745069 35099789203353019806654401)
        ·
          refine ⟨26324841902514764854990801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35099789203353019806654401 26324841902514764854990801)
          ·
            refine ⟨19743631426886073641243101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26324841902514764854990801 19743631426886073641243101)
            ·
              refine ⟨7403861785082277615466163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19743631426886073641243101 7403861785082277615466163)
              ·
                refine ⟨11105792677623416423199245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7403861785082277615466163 11105792677623416423199245)
                ·
                  refine ⟨4164672254108781158699717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11105792677623416423199245 4164672254108781158699717)
                  ·
                    refine ⟨780876047645396467256197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4164672254108781158699717 780876047645396467256197)
                    ·
                      rfl

theorem cell23_4562252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_4562252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562252 prefixEnd_4562252 := by exact prefixLift 4562252
  have htrace : WordTrace (prefixWord ++ tailWord_4562252) baseStart_4562252 baseEnd_4562252 := by
    simpa [prefixWord, tailWord_4562252, baseEnd_4562252] using wordTrace_append hprefix tailTrace_4562252
  have hstable : (prefixWord ++ tailWord_4562252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562252).length < 2 ^ (prefixWord ++ tailWord_4562252).sum := by decide
  have hdescent : baseEnd_4562252 < baseStart_4562252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562279 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_4562279 : Nat := 118140960795 + 4562279 * 2 ^ 59
def prefixEnd_4562279 : Nat := 4983230072969 + 3 ^ 40 * 4562279 * 2
def baseEnd_4562279 : Nat := 2342642006913860796130967

theorem tailTrace_4562279 : CollatzResearch.WordTrace tailWord_4562279 prefixEnd_4562279 2342642006913860796130967 := by
  unfold tailWord_4562279
  simp only [CollatzResearch.WordTrace]
  refine ⟨166399985438649833065001891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110933323625766555376667927 166399985438649833065001891)
  ·
    refine ⟨249599978157974749597502837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166399985438649833065001891 249599978157974749597502837)
    ·
      refine ⟨23399997952310132774765891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 249599978157974749597502837 23399997952310132774765891)
      ·
        refine ⟨35099996928465199162148837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23399997952310132774765891 35099996928465199162148837)
        ·
          refine ⟨6581249424087224842902907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35099996928465199162148837 6581249424087224842902907)
          ·
            refine ⟨9871874136130837264354361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6581249424087224842902907 9871874136130837264354361)
            ·
              refine ⟨7403905602098127948265771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9871874136130837264354361 7403905602098127948265771)
              ·
                refine ⟨11105858403147191922398657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7403905602098127948265771 11105858403147191922398657)
                ·
                  refine ⟨8329393802360393941798993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11105858403147191922398657 8329393802360393941798993)
                  ·
                    refine ⟨6247045351770295456349245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8329393802360393941798993 6247045351770295456349245)
                    ·
                      refine ⟨2342642006913860796130967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6247045351770295456349245 2342642006913860796130967)
                      ·
                        rfl

theorem cell23_4562279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_4562279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562279 prefixEnd_4562279 := by exact prefixLift 4562279
  have htrace : WordTrace (prefixWord ++ tailWord_4562279) baseStart_4562279 baseEnd_4562279 := by
    simpa [prefixWord, tailWord_4562279, baseEnd_4562279] using wordTrace_append hprefix tailTrace_4562279
  have hstable : (prefixWord ++ tailWord_4562279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562279).length < 2 ^ (prefixWord ++ tailWord_4562279).sum := by decide
  have hdescent : baseEnd_4562279 < baseStart_4562279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562315 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 4]
def baseStart_4562315 : Nat := 118140960795 + 4562315 * 2 ^ 59
def prefixEnd_4562315 : Nat := 4983230072969 + 3 ^ 40 * 4562315 * 2
def baseEnd_4562315 : Nat := 2342660492217422655280801

theorem tailTrace_4562315 : CollatzResearch.WordTrace tailWord_4562315 prefixEnd_4562315 2342660492217422655280801 := by
  unfold tailWord_4562315
  simp only [CollatzResearch.WordTrace]
  refine ⟨166401298466519411213312399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110934198977679607475541599 166401298466519411213312399)
  ·
    refine ⟨249601947699779116819968599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166401298466519411213312399 249601947699779116819968599)
    ·
      refine ⟨374402921549668675229952899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249601947699779116819968599 374402921549668675229952899)
      ·
        refine ⟨561604382324503012844929349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374402921549668675229952899 561604382324503012844929349)
        ·
          refine ⟨105300821685844314908424253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 561604382324503012844929349 105300821685844314908424253)
          ·
            refine ⟨39487808132191618090659095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105300821685844314908424253 39487808132191618090659095)
            ·
              refine ⟨59231712198287427135988643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39487808132191618090659095 59231712198287427135988643)
              ·
                refine ⟨88847568297431140703982965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59231712198287427135988643 88847568297431140703982965)
                ·
                  refine ⟨8329459527884169440998403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88847568297431140703982965 8329459527884169440998403)
                  ·
                    refine ⟨12494189291826254161497605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8329459527884169440998403 12494189291826254161497605)
                    ·
                      refine ⟨2342660492217422655280801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12494189291826254161497605 2342660492217422655280801)
                      ·
                        rfl

theorem cell23_4562315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 4].length) (baseStart_4562315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562315 prefixEnd_4562315 := by exact prefixLift 4562315
  have htrace : WordTrace (prefixWord ++ tailWord_4562315) baseStart_4562315 baseEnd_4562315 := by
    simpa [prefixWord, tailWord_4562315, baseEnd_4562315] using wordTrace_append hprefix tailTrace_4562315
  have hstable : (prefixWord ++ tailWord_4562315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562315).length < 2 ^ (prefixWord ++ tailWord_4562315).sum := by decide
  have hdescent : baseEnd_4562315 < baseStart_4562315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562325 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 1, 6]
def baseStart_4562325 : Nat := 118140960795 + 4562325 * 2 ^ 59
def prefixEnd_4562325 : Nat := 4983230072969 + 3 ^ 40 * 4562325 * 2
def baseEnd_4562325 : Nat := 780888542341322538718585

theorem tailTrace_4562325 : CollatzResearch.WordTrace tailWord_4562325 prefixEnd_4562325 780888542341322538718585 := by
  unfold tailWord_4562325
  simp only [CollatzResearch.WordTrace]
  refine ⟨166401663196483182921176429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110934442130988788614117619 166401663196483182921176429)
  ·
    refine ⟨62400623698681193595441161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166401663196483182921176429 62400623698681193595441161)
    ·
      refine ⟨46800467774010895196580871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62400623698681193595441161 46800467774010895196580871)
      ·
        refine ⟨70200701661016342794871307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46800467774010895196580871 70200701661016342794871307)
        ·
          refine ⟨105301052491524514192306961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70200701661016342794871307 105301052491524514192306961)
          ·
            refine ⟨78975789368643385644230221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105301052491524514192306961 78975789368643385644230221)
            ·
              refine ⟨29615921013241269616586333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78975789368643385644230221 29615921013241269616586333)
              ·
                refine ⟨11105970379965476106219875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29615921013241269616586333 11105970379965476106219875)
                ·
                  refine ⟨16658955569948214159329813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11105970379965476106219875 16658955569948214159329813)
                  ·
                    refine ⟨780888542341322538718585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16658955569948214159329813 780888542341322538718585)
                    ·
                      rfl

theorem cell23_4562325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_4562325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562325 prefixEnd_4562325 := by exact prefixLift 4562325
  have htrace : WordTrace (prefixWord ++ tailWord_4562325) baseStart_4562325 baseEnd_4562325 := by
    simpa [prefixWord, tailWord_4562325, baseEnd_4562325] using wordTrace_append hprefix tailTrace_4562325
  have hstable : (prefixWord ++ tailWord_4562325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562325).length < 2 ^ (prefixWord ++ tailWord_4562325).sum := by decide
  have hdescent : baseEnd_4562325 < baseStart_4562325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562415 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 4, 6]
def baseStart_4562415 : Nat := 118140960795 + 4562415 * 2 ^ 59
def prefixEnd_4562415 : Nat := 4983230072969 + 3 ^ 40 * 4562415 * 2
def baseEnd_4562415 : Nat := 780903946760957421343447

theorem tailTrace_4562415 : CollatzResearch.WordTrace tailWord_4562415 prefixEnd_4562415 780903946760957421343447 := by
  unfold tailWord_4562415
  simp only [CollatzResearch.WordTrace]
  refine ⟨166404945766157128291952699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110936630510771418861301799 166404945766157128291952699)
  ·
    refine ⟨249607418649235692437929049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166404945766157128291952699 249607418649235692437929049)
    ·
      refine ⟨187205563986926769328446787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249607418649235692437929049 187205563986926769328446787)
      ·
        refine ⟨280808345980390153992670181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187205563986926769328446787 280808345980390153992670181)
        ·
          refine ⟨52651564871323153873625659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 280808345980390153992670181 52651564871323153873625659)
          ·
            refine ⟨78977347306984730810438489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52651564871323153873625659 78977347306984730810438489)
            ·
              refine ⟨59233010480238548107828867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78977347306984730810438489 59233010480238548107828867)
              ·
                refine ⟨88849515720357822161743301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59233010480238548107828867 88849515720357822161743301)
                ·
                  refine ⟨16659284197567091655326869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88849515720357822161743301 16659284197567091655326869)
                  ·
                    refine ⟨780903946760957421343447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16659284197567091655326869 780903946760957421343447)
                    ·
                      rfl

theorem cell23_4562415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 6].length) (baseStart_4562415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562415 prefixEnd_4562415 := by exact prefixLift 4562415
  have htrace : WordTrace (prefixWord ++ tailWord_4562415) baseStart_4562415 baseEnd_4562415 := by
    simpa [prefixWord, tailWord_4562415, baseEnd_4562415] using wordTrace_append hprefix tailTrace_4562415
  have hstable : (prefixWord ++ tailWord_4562415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562415).length < 2 ^ (prefixWord ++ tailWord_4562415).sum := by decide
  have hdescent : baseEnd_4562415 < baseStart_4562415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562425 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 3, 3, 5]
def baseStart_4562425 : Nat := 118140960795 + 4562425 * 2 ^ 59
def prefixEnd_4562425 : Nat := 4983230072969 + 3 ^ 40 * 4562425 * 2
def baseEnd_4562425 : Nat := 2342716975089417224905295

theorem tailTrace_4562425 : CollatzResearch.WordTrace tailWord_4562425 prefixEnd_4562425 2342716975089417224905295 := by
  unfold tailWord_4562425
  simp only [CollatzResearch.WordTrace]
  refine ⟨166405310496120899999816729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110936873664080599999877819 166405310496120899999816729)
  ·
    refine ⟨124803982872090674999862547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166405310496120899999816729 124803982872090674999862547)
    ·
      refine ⟨187205974308136012499793821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124803982872090674999862547 187205974308136012499793821)
      ·
        refine ⟨70202240365551004687422683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187205974308136012499793821 70202240365551004687422683)
        ·
          refine ⟨105303360548326507031134025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70202240365551004687422683 105303360548326507031134025)
          ·
            refine ⟨78977520411244880273350519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105303360548326507031134025 78977520411244880273350519)
            ·
              refine ⟨118466280616867320410025779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78977520411244880273350519 118466280616867320410025779)
              ·
                refine ⟨177699420925300980615038669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118466280616867320410025779 177699420925300980615038669)
                ·
                  refine ⟨66637282846987867730639501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177699420925300980615038669 66637282846987867730639501)
                  ·
                    refine ⟨24988981067620450398989813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66637282846987867730639501 24988981067620450398989813)
                    ·
                      refine ⟨2342716975089417224905295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24988981067620450398989813 2342716975089417224905295)
                      ·
                        rfl

theorem cell23_4562425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_4562425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562425 prefixEnd_4562425 := by exact prefixLift 4562425
  have htrace : WordTrace (prefixWord ++ tailWord_4562425) baseStart_4562425 baseEnd_4562425 := by
    simpa [prefixWord, tailWord_4562425, baseEnd_4562425] using wordTrace_append hprefix tailTrace_4562425
  have hstable : (prefixWord ++ tailWord_4562425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562425).length < 2 ^ (prefixWord ++ tailWord_4562425).sum := by decide
  have hdescent : baseEnd_4562425 < baseStart_4562425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562442 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_4562442 : Nat := 118140960795 + 4562442 * 2 ^ 59
def prefixEnd_4562442 : Nat := 4983230072969 + 3 ^ 40 * 4562442 * 2
def baseEnd_4562442 : Nat := 2342725704260543658392717

theorem tailTrace_4562442 : CollatzResearch.WordTrace tailWord_4562442 prefixEnd_4562442 2342725704260543658392717 := by
  unfold tailWord_4562442
  simp only [CollatzResearch.WordTrace]
  refine ⟨41601482634264827975796395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110937287024706207935457053 41601482634264827975796395)
  ·
    refine ⟨62402223951397241963694593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41601482634264827975796395 62402223951397241963694593)
    ·
      refine ⟨46801667963547931472770945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62402223951397241963694593 46801667963547931472770945)
      ·
        refine ⟨35101250972660948604578209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46801667963547931472770945 35101250972660948604578209)
        ·
          refine ⟨26325938229495711453433657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35101250972660948604578209 26325938229495711453433657)
          ·
            refine ⟨19744453672121783590075243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26325938229495711453433657 19744453672121783590075243)
            ·
              refine ⟨29616680508182675385112865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19744453672121783590075243 29616680508182675385112865)
              ·
                refine ⟨22212510381137006538834649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29616680508182675385112865 22212510381137006538834649)
                ·
                  refine ⟨16659382785852754904125987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22212510381137006538834649 16659382785852754904125987)
                  ·
                    refine ⟨24989074178779132356188981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16659382785852754904125987 24989074178779132356188981)
                    ·
                      refine ⟨2342725704260543658392717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24989074178779132356188981 2342725704260543658392717)
                      ·
                        rfl

theorem cell23_4562442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_4562442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562442 prefixEnd_4562442 := by exact prefixLift 4562442
  have htrace : WordTrace (prefixWord ++ tailWord_4562442) baseStart_4562442 baseEnd_4562442 := by
    simpa [prefixWord, tailWord_4562442, baseEnd_4562442] using wordTrace_append hprefix tailTrace_4562442
  have hstable : (prefixWord ++ tailWord_4562442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562442).length < 2 ^ (prefixWord ++ tailWord_4562442).sum := by decide
  have hdescent : baseEnd_4562442 < baseStart_4562442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562443 : List Nat := [1, 1, 1, 1, 8, 2, 1, 2, 1, 3, 2]
def baseStart_4562443 : Nat := 118140960795 + 4562443 * 2 ^ 59
def prefixEnd_4562443 : Nat := 4983230072969 + 3 ^ 40 * 4562443 * 2
def baseEnd_4562443 : Nat := 2342726217741198154480213

theorem tailTrace_4562443 : CollatzResearch.WordTrace tailWord_4562443 prefixEnd_4562443 2342726217741198154480213 := by
  unfold tailWord_4562443
  simp only [CollatzResearch.WordTrace]
  refine ⟨166405967010055689073971983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110937311340037126049314655 166405967010055689073971983)
  ·
    refine ⟨249608950515083533610957975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166405967010055689073971983 249608950515083533610957975)
    ·
      refine ⟨374413425772625300416436963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249608950515083533610957975 374413425772625300416436963)
      ·
        refine ⟨561620138658937950624655445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374413425772625300416436963 561620138658937950624655445)
        ·
          refine ⟨6581485999909429108882681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 561620138658937950624655445 6581485999909429108882681)
          ·
            refine ⟨4936114499932071831662011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6581485999909429108882681 4936114499932071831662011)
            ·
              refine ⟨7404171749898107747493017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4936114499932071831662011 7404171749898107747493017)
              ·
                refine ⟨5553128812423580810619763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7404171749898107747493017 5553128812423580810619763)
                ·
                  refine ⟨8329693218635371215929645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5553128812423580810619763 8329693218635371215929645)
                  ·
                    refine ⟨3123634956988264205973617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8329693218635371215929645 3123634956988264205973617)
                    ·
                      refine ⟨2342726217741198154480213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3123634956988264205973617 2342726217741198154480213)
                      ·
                        rfl

theorem cell23_4562443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 3, 2].length) (baseStart_4562443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562443 prefixEnd_4562443 := by exact prefixLift 4562443
  have htrace : WordTrace (prefixWord ++ tailWord_4562443) baseStart_4562443 baseEnd_4562443 := by
    simpa [prefixWord, tailWord_4562443, baseEnd_4562443] using wordTrace_append hprefix tailTrace_4562443
  have hstable : (prefixWord ++ tailWord_4562443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562443).length < 2 ^ (prefixWord ++ tailWord_4562443).sum := by decide
  have hdescent : baseEnd_4562443 < baseStart_4562443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562456 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 1, 4, 2]
def baseStart_4562456 : Nat := 118140960795 + 4562456 * 2 ^ 59
def prefixEnd_4562456 : Nat := 4983230072969 + 3 ^ 40 * 4562456 * 2
def baseEnd_4562456 : Nat := 2342732892989706603617653

theorem tailTrace_4562456 : CollatzResearch.WordTrace tailWord_4562456 prefixEnd_4562456 2342732892989706603617653 := by
  unfold tailWord_4562456
  simp only [CollatzResearch.WordTrace]
  refine ⟨83203220579504296147097611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110937627439339061529463481 83203220579504296147097611)
  ·
    refine ⟨124804830869256444220646417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83203220579504296147097611 124804830869256444220646417)
    ·
      refine ⟨93603623151942333165484813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124804830869256444220646417 93603623151942333165484813)
      ·
        refine ⟨35101358681978374937056805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93603623151942333165484813 35101358681978374937056805)
        ·
          refine ⟨6581504752870945300698151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35101358681978374937056805 6581504752870945300698151)
          ·
            refine ⟨9872257129306417951047227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6581504752870945300698151 9872257129306417951047227)
            ·
              refine ⟨14808385693959626926570841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9872257129306417951047227 14808385693959626926570841)
              ·
                refine ⟨11106289270469720194928131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14808385693959626926570841 11106289270469720194928131)
                ·
                  refine ⟨16659433905704580292392197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11106289270469720194928131 16659433905704580292392197)
                  ·
                    refine ⟨3123643857319608804823537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16659433905704580292392197 3123643857319608804823537)
                    ·
                      refine ⟨2342732892989706603617653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3123643857319608804823537 2342732892989706603617653)
                      ·
                        rfl

theorem cell23_4562456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_4562456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562456 prefixEnd_4562456 := by exact prefixLift 4562456
  have htrace : WordTrace (prefixWord ++ tailWord_4562456) baseStart_4562456 baseEnd_4562456 := by
    simpa [prefixWord, tailWord_4562456, baseEnd_4562456] using wordTrace_append hprefix tailTrace_4562456
  have hstable : (prefixWord ++ tailWord_4562456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562456).length < 2 ^ (prefixWord ++ tailWord_4562456).sum := by decide
  have hdescent : baseEnd_4562456 < baseStart_4562456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562475 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 5, 7]
def baseStart_4562475 : Nat := 118140960795 + 4562475 * 2 ^ 59
def prefixEnd_4562475 : Nat := 4983230072969 + 3 ^ 40 * 4562475 * 2
def baseEnd_4562475 : Nat := 780914216374047343093355

theorem tailTrace_4562475 : CollatzResearch.WordTrace tailWord_4562475 prefixEnd_4562475 780914216374047343093355 := by
  unfold tailWord_4562475
  simp only [CollatzResearch.WordTrace]
  refine ⟨166407134145939758539136879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110938089430626505692757919 166407134145939758539136879)
  ·
    refine ⟨249610701218909637808705319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166407134145939758539136879 249610701218909637808705319)
    ·
      refine ⟨374416051828364456713057979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249610701218909637808705319 374416051828364456713057979)
      ·
        refine ⟨561624077742546685069586969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374416051828364456713057979 561624077742546685069586969)
        ·
          refine ⟨421218058306910013802190227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 561624077742546685069586969 421218058306910013802190227)
          ·
            refine ⟨631827087460365020703285341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421218058306910013802190227 631827087460365020703285341)
            ·
              refine ⟨236935157797636882763732003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 631827087460365020703285341 236935157797636882763732003)
              ·
                refine ⟨355402736696455324145598005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236935157797636882763732003 355402736696455324145598005)
                ·
                  refine ⟨33319006565292686638649813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 355402736696455324145598005 33319006565292686638649813)
                  ·
                    refine ⟨780914216374047343093355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33319006565292686638649813 780914216374047343093355)
                    ·
                      rfl

theorem cell23_4562475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 7].length) (baseStart_4562475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562475 prefixEnd_4562475 := by exact prefixLift 4562475
  have htrace : WordTrace (prefixWord ++ tailWord_4562475) baseStart_4562475 baseEnd_4562475 := by
    simpa [prefixWord, tailWord_4562475, baseEnd_4562475] using wordTrace_append hprefix tailTrace_4562475
  have hstable : (prefixWord ++ tailWord_4562475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562475).length < 2 ^ (prefixWord ++ tailWord_4562475).sum := by decide
  have hdescent : baseEnd_4562475 < baseStart_4562475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562486 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_4562486 : Nat := 118140960795 + 4562486 * 2 ^ 59
def prefixEnd_4562486 : Nat := 4983230072969 + 3 ^ 40 * 4562486 * 2
def baseEnd_4562486 : Nat := 2342748297409341486242515

theorem tailTrace_4562486 : CollatzResearch.WordTrace tailWord_4562486 prefixEnd_4562486 2342748297409341486242515 := by
  unfold tailWord_4562486
  simp only [CollatzResearch.WordTrace]
  refine ⟨10400470959306244213611707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110938356899266604945191541 10400470959306244213611707)
  ·
    refine ⟨15600706438959366320417561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10400470959306244213611707 15600706438959366320417561)
    ·
      refine ⟨11700529829219524740313171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15600706438959366320417561 11700529829219524740313171)
      ·
        refine ⟨17550794743829287110469757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11700529829219524740313171 17550794743829287110469757)
        ·
          refine ⟨6581548028935982666426159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17550794743829287110469757 6581548028935982666426159)
          ·
            refine ⟨9872322043403973999639239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6581548028935982666426159 9872322043403973999639239)
            ·
              refine ⟨14808483065105960999458859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9872322043403973999639239 14808483065105960999458859)
              ·
                refine ⟨22212724597658941499188289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14808483065105960999458859 22212724597658941499188289)
                ·
                  refine ⟨16659543448244206124391217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22212724597658941499188289 16659543448244206124391217)
                  ·
                    refine ⟨12494657586183154593293413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16659543448244206124391217 12494657586183154593293413)
                    ·
                      refine ⟨2342748297409341486242515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12494657586183154593293413 2342748297409341486242515)
                      ·
                        rfl

theorem cell23_4562486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_4562486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562486 prefixEnd_4562486 := by exact prefixLift 4562486
  have htrace : WordTrace (prefixWord ++ tailWord_4562486) baseStart_4562486 baseEnd_4562486 := by
    simpa [prefixWord, tailWord_4562486, baseEnd_4562486] using wordTrace_append hprefix tailTrace_4562486
  have hstable : (prefixWord ++ tailWord_4562486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562486).length < 2 ^ (prefixWord ++ tailWord_4562486).sum := by decide
  have hdescent : baseEnd_4562486 < baseStart_4562486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562489 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 2, 3, 3]
def baseStart_4562489 : Nat := 118140960795 + 4562489 * 2 ^ 59
def prefixEnd_4562489 : Nat := 4983230072969 + 3 ^ 40 * 4562489 * 2
def baseEnd_4562489 : Nat := 2342749837851304974505001

theorem tailTrace_4562489 : CollatzResearch.WordTrace tailWord_4562489 prefixEnd_4562489 2342749837851304974505001 := by
  unfold tailWord_4562489
  simp only [CollatzResearch.WordTrace]
  refine ⟨166407644767889038930146521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110938429845259359286764347 166407644767889038930146521)
  ·
    refine ⟨124805733575916779197609891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166407644767889038930146521 124805733575916779197609891)
    ·
      refine ⟨187208600363875168796414837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124805733575916779197609891 187208600363875168796414837)
      ·
        refine ⟨17550806284113297074663891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 187208600363875168796414837 17550806284113297074663891)
        ·
          refine ⟨26326209426169945611995837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17550806284113297074663891 26326209426169945611995837)
          ·
            refine ⟨9872328534813729604498439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26326209426169945611995837 9872328534813729604498439)
            ·
              refine ⟨14808492802220594406747659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9872328534813729604498439 14808492802220594406747659)
              ·
                refine ⟨22212739203330891610121489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14808492802220594406747659 22212739203330891610121489)
                ·
                  refine ⟨16659554402498168707591117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22212739203330891610121489 16659554402498168707591117)
                  ·
                    refine ⟨6247332900936813265346669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16659554402498168707591117 6247332900936813265346669)
                    ·
                      refine ⟨2342749837851304974505001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6247332900936813265346669 2342749837851304974505001)
                      ·
                        rfl

theorem cell23_4562489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_4562489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562489 prefixEnd_4562489 := by exact prefixLift 4562489
  have htrace : WordTrace (prefixWord ++ tailWord_4562489) baseStart_4562489 baseEnd_4562489 := by
    simpa [prefixWord, tailWord_4562489, baseEnd_4562489] using wordTrace_append hprefix tailTrace_4562489
  have hstable : (prefixWord ++ tailWord_4562489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562489).length < 2 ^ (prefixWord ++ tailWord_4562489).sum := by decide
  have hdescent : baseEnd_4562489 < baseStart_4562489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562512 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 4]
def baseStart_4562512 : Nat := 118140960795 + 4562512 * 2 ^ 59
def prefixEnd_4562512 : Nat := 4983230072969 + 3 ^ 40 * 4562512 * 2
def baseEnd_4562512 : Nat := 2342761647906358384517395

theorem tailTrace_4562512 : CollatzResearch.WordTrace tailWord_4562512 prefixEnd_4562512 2342761647906358384517395 := by
  unfold tailWord_4562512
  simp only [CollatzResearch.WordTrace]
  refine ⟨83204241823402856929116895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110938989097870475905489193 83204241823402856929116895)
  ·
    refine ⟨124806362735104285393675343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83204241823402856929116895 124806362735104285393675343)
    ·
      refine ⟨187209544102656428090513015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124806362735104285393675343 187209544102656428090513015)
      ·
        refine ⟨280814316153984642135769523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187209544102656428090513015 280814316153984642135769523)
        ·
          refine ⟨421221474230976963203654285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280814316153984642135769523 421221474230976963203654285)
          ·
            refine ⟨157958052836616361201370357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 421221474230976963203654285 157958052836616361201370357)
            ·
              refine ⟨14808567453432783862628471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 157958052836616361201370357 14808567453432783862628471)
              ·
                refine ⟨22212851180149175793942707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14808567453432783862628471 22212851180149175793942707)
                ·
                  refine ⟨33319276770223763690914061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22212851180149175793942707 33319276770223763690914061)
                  ·
                    refine ⟨12494728788833911384092773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33319276770223763690914061 12494728788833911384092773)
                    ·
                      refine ⟨2342761647906358384517395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12494728788833911384092773 2342761647906358384517395)
                      ·
                        rfl

theorem cell23_4562512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_4562512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562512 prefixEnd_4562512 := by exact prefixLift 4562512
  have htrace : WordTrace (prefixWord ++ tailWord_4562512) baseStart_4562512 baseEnd_4562512 := by
    simpa [prefixWord, tailWord_4562512, baseEnd_4562512] using wordTrace_append hprefix tailTrace_4562512
  have hstable : (prefixWord ++ tailWord_4562512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562512).length < 2 ^ (prefixWord ++ tailWord_4562512).sum := by decide
  have hdescent : baseEnd_4562512 < baseStart_4562512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562529 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 4, 4, 2]
def baseStart_4562529 : Nat := 118140960795 + 4562529 * 2 ^ 59
def prefixEnd_4562529 : Nat := 4983230072969 + 3 ^ 40 * 4562529 * 2
def baseEnd_4562529 : Nat := 2342770377077484818004817

theorem tailTrace_4562529 : CollatzResearch.WordTrace tailWord_4562529 prefixEnd_4562529 2342770377077484818004817 := by
  unfold tailWord_4562529
  simp only [CollatzResearch.WordTrace]
  refine ⟨166409103687744125761602641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110939402458496083841068427 166409103687744125761602641)
  ·
    refine ⟨124806827765808094321201981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166409103687744125761602641 124806827765808094321201981)
    ·
      refine ⟨46802560412178035370450743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124806827765808094321201981 46802560412178035370450743)
      ·
        refine ⟨70203840618267053055676115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46802560412178035370450743 70203840618267053055676115)
        ·
          refine ⟨105305760927400579583514173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70203840618267053055676115 105305760927400579583514173)
          ·
            refine ⟨39489660347775217343817815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105305760927400579583514173 39489660347775217343817815)
            ·
              refine ⟨59234490521662826015726723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39489660347775217343817815 59234490521662826015726723)
              ·
                refine ⟨88851735782494239023590085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59234490521662826015726723 88851735782494239023590085)
                ·
                  refine ⟨16659700459217669816923141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88851735782494239023590085 16659700459217669816923141)
                  ·
                    refine ⟨3123693836103313090673089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16659700459217669816923141 3123693836103313090673089)
                    ·
                      refine ⟨2342770377077484818004817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3123693836103313090673089 2342770377077484818004817)
                      ·
                        rfl

theorem cell23_4562529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_4562529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562529 prefixEnd_4562529 := by exact prefixLift 4562529
  have htrace : WordTrace (prefixWord ++ tailWord_4562529) baseStart_4562529 baseEnd_4562529 := by
    simpa [prefixWord, tailWord_4562529, baseEnd_4562529] using wordTrace_append hprefix tailTrace_4562529
  have hstable : (prefixWord ++ tailWord_4562529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562529).length < 2 ^ (prefixWord ++ tailWord_4562529).sum := by decide
  have hdescent : baseEnd_4562529 < baseStart_4562529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562546 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 2, 4, 2]
def baseStart_4562546 : Nat := 118140960795 + 4562546 * 2 ^ 59
def prefixEnd_4562546 : Nat := 4983230072969 + 3 ^ 40 * 4562546 * 2
def baseEnd_4562546 : Nat := 2342779106248611251492239

theorem tailTrace_4562546 : CollatzResearch.WordTrace tailWord_4562546 prefixEnd_4562546 2342779106248611251492239 := by
  unfold tailWord_4562546
  simp only [CollatzResearch.WordTrace]
  refine ⟨41602430932170634416242873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110939815819121691776647661 41602430932170634416242873)
  ·
    refine ⟨31201823199127975812182155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41602430932170634416242873 31201823199127975812182155)
    ·
      refine ⟨46802734798691963718273233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31201823199127975812182155 46802734798691963718273233)
      ·
        refine ⟨35102051099018972788704925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46802734798691963718273233 35102051099018972788704925)
        ·
          refine ⟨13163269162132114795764347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35102051099018972788704925 13163269162132114795764347)
          ·
            refine ⟨19744903743198172193646521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13163269162132114795764347 19744903743198172193646521)
            ·
              refine ⟨14808677807398629145234891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19744903743198172193646521 14808677807398629145234891)
              ·
                refine ⟨22213016711097943717852337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14808677807398629145234891 22213016711097943717852337)
                ·
                  refine ⟨16659762533323457788389253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22213016711097943717852337 16659762533323457788389253)
                  ·
                    refine ⟨3123705474998148335322985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16659762533323457788389253 3123705474998148335322985)
                    ·
                      refine ⟨2342779106248611251492239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3123705474998148335322985 2342779106248611251492239)
                      ·
                        rfl

theorem cell23_4562546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_4562546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562546 prefixEnd_4562546 := by exact prefixLift 4562546
  have htrace : WordTrace (prefixWord ++ tailWord_4562546) baseStart_4562546 baseEnd_4562546 := by
    simpa [prefixWord, tailWord_4562546, baseEnd_4562546] using wordTrace_append hprefix tailTrace_4562546
  have hstable : (prefixWord ++ tailWord_4562546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562546).length < 2 ^ (prefixWord ++ tailWord_4562546).sum := by decide
  have hdescent : baseEnd_4562546 < baseStart_4562546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562619 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 2, 6, 2]
def baseStart_4562619 : Nat := 118140960795 + 4562619 * 2 ^ 59
def prefixEnd_4562619 : Nat := 4983230072969 + 3 ^ 40 * 4562619 * 2
def baseEnd_4562619 : Nat := 2342816590336389465879403

theorem tailTrace_4562619 : CollatzResearch.WordTrace tailWord_4562619 prefixEnd_4562619 2342816590336389465879403 := by
  unfold tailWord_4562619
  simp only [CollatzResearch.WordTrace]
  refine ⟨166412386257418071132378911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110941590838278714088252607 166412386257418071132378911)
  ·
    refine ⟨249618579386127106698568367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166412386257418071132378911 249618579386127106698568367)
    ·
      refine ⟨374427869079190660047852551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249618579386127106698568367 374427869079190660047852551)
      ·
        refine ⟨561641803618785990071778827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374427869079190660047852551 561641803618785990071778827)
        ·
          refine ⟨842462705428178985107668241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561641803618785990071778827 842462705428178985107668241)
          ·
            refine ⟨631847029071134238830751181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 842462705428178985107668241 631847029071134238830751181)
            ·
              refine ⟨236942635901675339561531693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 631847029071134238830751181 236942635901675339561531693)
              ·
                refine ⟨88853488463128252335574385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 236942635901675339561531693 88853488463128252335574385)
                ·
                  refine ⟨66640116347346189251680789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88853488463128252335574385 66640116347346189251680789)
                  ·
                    refine ⟨3123755453781852621172537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66640116347346189251680789 3123755453781852621172537)
                    ·
                      refine ⟨2342816590336389465879403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3123755453781852621172537 2342816590336389465879403)
                      ·
                        rfl

theorem cell23_4562619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 6, 2].length) (baseStart_4562619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562619 prefixEnd_4562619 := by exact prefixLift 4562619
  have htrace : WordTrace (prefixWord ++ tailWord_4562619) baseStart_4562619 baseEnd_4562619 := by
    simpa [prefixWord, tailWord_4562619, baseEnd_4562619] using wordTrace_append hprefix tailTrace_4562619
  have hstable : (prefixWord ++ tailWord_4562619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562619).length < 2 ^ (prefixWord ++ tailWord_4562619).sum := by decide
  have hdescent : baseEnd_4562619 < baseStart_4562619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562663 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 1, 6]
def baseStart_4562663 : Nat := 118140960795 + 4562663 * 2 ^ 59
def prefixEnd_4562663 : Nat := 4983230072969 + 3 ^ 40 * 4562663 * 2
def baseEnd_4562663 : Nat := 780946394495062431243067

theorem tailTrace_4562663 : CollatzResearch.WordTrace tailWord_4562663 prefixEnd_4562663 780946394495062431243067 := by
  unfold tailWord_4562663
  simp only [CollatzResearch.WordTrace]
  refine ⟨166413991069258666646980643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110942660712839111097987095 166413991069258666646980643)
  ·
    refine ⟨249620986603887999970470965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166413991069258666646980643 249620986603887999970470965)
    ·
      refine ⟨23401967494114499997231653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 249620986603887999970470965 23401967494114499997231653)
      ·
        refine ⟨4387868905146468749480935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23401967494114499997231653 4387868905146468749480935)
        ·
          refine ⟨6581803357719703124221403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4387868905146468749480935 6581803357719703124221403)
          ·
            refine ⟨9872705036579554686332105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6581803357719703124221403 9872705036579554686332105)
            ·
              refine ⟨7404528777434666014749079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9872705036579554686332105 7404528777434666014749079)
              ·
                refine ⟨11106793166151999022123619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7404528777434666014749079 11106793166151999022123619)
                ·
                  refine ⟨16660189749227998533185429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11106793166151999022123619 16660189749227998533185429)
                  ·
                    refine ⟨780946394495062431243067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16660189749227998533185429 780946394495062431243067)
                    ·
                      rfl

theorem cell23_4562663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_4562663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562663 prefixEnd_4562663 := by exact prefixLift 4562663
  have htrace : WordTrace (prefixWord ++ tailWord_4562663) baseStart_4562663 baseEnd_4562663 := by
    simpa [prefixWord, tailWord_4562663, baseEnd_4562663] using wordTrace_append hprefix tailTrace_4562663
  have hstable : (prefixWord ++ tailWord_4562663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562663).length < 2 ^ (prefixWord ++ tailWord_4562663).sum := by decide
  have hdescent : baseEnd_4562663 < baseStart_4562663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562719 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 2, 6]
def baseStart_4562719 : Nat := 118140960795 + 4562719 * 2 ^ 59
def prefixEnd_4562719 : Nat := 4983230072969 + 3 ^ 40 * 4562719 * 2
def baseEnd_4562719 : Nat := 780955979467279691542981

theorem tailTrace_4562719 : CollatzResearch.WordTrace tailWord_4562719 prefixEnd_4562719 780955979467279691542981 := by
  unfold tailWord_4562719
  simp only [CollatzResearch.WordTrace]
  refine ⟨166416033557055788211019211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110944022371370525474012807 166416033557055788211019211)
  ·
    refine ⟨249624050335583682316528817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166416033557055788211019211 249624050335583682316528817)
    ·
      refine ⟨187218037751687761737396613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249624050335583682316528817 187218037751687761737396613)
      ·
        refine ⟨35103382078441455325761865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187218037751687761737396613 35103382078441455325761865)
        ·
          refine ⟨26327536558831091494321399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35103382078441455325761865 26327536558831091494321399)
          ·
            refine ⟨39491304838246637241482099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26327536558831091494321399 39491304838246637241482099)
            ·
              refine ⟨59236957257369955862223149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39491304838246637241482099 59236957257369955862223149)
              ·
                refine ⟨22213858971513733448333681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59236957257369955862223149 22213858971513733448333681)
                ·
                  refine ⟨16660394228635300086250261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22213858971513733448333681 16660394228635300086250261)
                  ·
                    refine ⟨780955979467279691542981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16660394228635300086250261 780955979467279691542981)
                    ·
                      rfl

theorem cell23_4562719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 6].length) (baseStart_4562719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562719 prefixEnd_4562719 := by exact prefixLift 4562719
  have htrace : WordTrace (prefixWord ++ tailWord_4562719) baseStart_4562719 baseEnd_4562719 := by
    simpa [prefixWord, tailWord_4562719, baseEnd_4562719] using wordTrace_append hprefix tailTrace_4562719
  have hstable : (prefixWord ++ tailWord_4562719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562719).length < 2 ^ (prefixWord ++ tailWord_4562719).sum := by decide
  have hdescent : baseEnd_4562719 < baseStart_4562719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562720 : List Nat := [2, 1, 1, 5, 1, 1, 5, 1, 2, 1, 3]
def baseStart_4562720 : Nat := 118140960795 + 4562720 * 2 ^ 59
def prefixEnd_4562720 : Nat := 4983230072969 + 3 ^ 40 * 4562720 * 2
def baseEnd_4562720 : Nat := 2342868451882493570716439

theorem tailTrace_4562720 : CollatzResearch.WordTrace tailWord_4562720 prefixEnd_4562720 2342868451882493570716439 := by
  unfold tailWord_4562720
  simp only [CollatzResearch.WordTrace]
  refine ⟨83208035015026082690902807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110944046686701443587870409 83208035015026082690902807)
  ·
    refine ⟨124812052522539124036354211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83208035015026082690902807 124812052522539124036354211)
    ·
      refine ⟨187218078783808686054531317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124812052522539124036354211 187218078783808686054531317)
      ·
        refine ⟨17551694885982064317612311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 187218078783808686054531317 17551694885982064317612311)
        ·
          refine ⟨26327542328973096476418467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17551694885982064317612311 26327542328973096476418467)
          ·
            refine ⟨39491313493459644714627701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26327542328973096476418467 39491313493459644714627701)
            ·
              refine ⟨3702310640011841691996347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39491313493459644714627701 3702310640011841691996347)
              ·
                refine ⟨5553465960017762537994521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3702310640011841691996347 5553465960017762537994521)
                ·
                  refine ⟨4165099470013321903495891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5553465960017762537994521 4165099470013321903495891)
                  ·
                    refine ⟨6247649205019982855243837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4165099470013321903495891 6247649205019982855243837)
                    ·
                      refine ⟨2342868451882493570716439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6247649205019982855243837 2342868451882493570716439)
                      ·
                        rfl

theorem cell23_4562720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_4562720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562720 prefixEnd_4562720 := by exact prefixLift 4562720
  have htrace : WordTrace (prefixWord ++ tailWord_4562720) baseStart_4562720 baseEnd_4562720 := by
    simpa [prefixWord, tailWord_4562720, baseEnd_4562720] using wordTrace_append hprefix tailTrace_4562720
  have hstable : (prefixWord ++ tailWord_4562720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562720).length < 2 ^ (prefixWord ++ tailWord_4562720).sum := by decide
  have hdescent : baseEnd_4562720 < baseStart_4562720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562746 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5]
def baseStart_4562746 : Nat := 118140960795 + 4562746 * 2 ^ 59
def prefixEnd_4562746 : Nat := 4983230072969 + 3 ^ 40 * 4562746 * 2
def baseEnd_4562746 : Nat := 2342881802379510468991319

theorem tailTrace_4562746 : CollatzResearch.WordTrace tailWord_4562746 prefixEnd_4562746 2342881802379510468991319 := by
  unfold tailWord_4562746
  simp only [CollatzResearch.WordTrace]
  refine ⟨41604254581989492955563023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110944678885305314548168061 41604254581989492955563023)
  ·
    refine ⟨62406381872984239433344535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41604254581989492955563023 62406381872984239433344535)
    ·
      refine ⟨93609572809476359150016803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62406381872984239433344535 93609572809476359150016803)
      ·
        refine ⟨140414359214214538725025205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93609572809476359150016803 140414359214214538725025205)
        ·
          refine ⟨13163846176332613005471113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140414359214214538725025205 13163846176332613005471113)
          ·
            refine ⟨9872884632249459754103335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13163846176332613005471113 9872884632249459754103335)
            ·
              refine ⟨14809326948374189631155003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9872884632249459754103335 14809326948374189631155003)
              ·
                refine ⟨22213990422561284446732505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14809326948374189631155003 22213990422561284446732505)
                ·
                  refine ⟨16660492816920963335049379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22213990422561284446732505 16660492816920963335049379)
                  ·
                    refine ⟨24990739225381445002574069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16660492816920963335049379 24990739225381445002574069)
                    ·
                      refine ⟨2342881802379510468991319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24990739225381445002574069 2342881802379510468991319)
                      ·
                        rfl

theorem cell23_4562746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_4562746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562746 prefixEnd_4562746 := by exact prefixLift 4562746
  have htrace : WordTrace (prefixWord ++ tailWord_4562746) baseStart_4562746 baseEnd_4562746 := by
    simpa [prefixWord, tailWord_4562746, baseEnd_4562746] using wordTrace_append hprefix tailTrace_4562746
  have hstable : (prefixWord ++ tailWord_4562746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562746).length < 2 ^ (prefixWord ++ tailWord_4562746).sum := by decide
  have hdescent : baseEnd_4562746 < baseStart_4562746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562789 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 7]
def baseStart_4562789 : Nat := 118140960795 + 4562789 * 2 ^ 59
def prefixEnd_4562789 : Nat := 4983230072969 + 3 ^ 40 * 4562789 * 2
def baseEnd_4562789 : Nat := 2342903882047653800753621

theorem tailTrace_4562789 : CollatzResearch.WordTrace tailWord_4562789 prefixEnd_4562789 2342903882047653800753621 := by
  unfold tailWord_4562789
  simp only [CollatzResearch.WordTrace]
  refine ⟨166418586666802190166067421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110945724444534793444044947 166418586666802190166067421)
  ·
    refine ⟨62406970000050821312275283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166418586666802190166067421 62406970000050821312275283)
    ·
      refine ⟨93610455000076231968412925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62406970000050821312275283 93610455000076231968412925)
      ·
        refine ⟨35103920625028586988154847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93610455000076231968412925 35103920625028586988154847)
        ·
          refine ⟨52655880937542880482232271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35103920625028586988154847 52655880937542880482232271)
          ·
            refine ⟨78983821406314320723348407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52655880937542880482232271 78983821406314320723348407)
            ·
              refine ⟨118475732109471481085022611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78983821406314320723348407 118475732109471481085022611)
              ·
                refine ⟨177713598164207221627533917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118475732109471481085022611 177713598164207221627533917)
                ·
                  refine ⟨66642599311577708110325219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177713598164207221627533917 66642599311577708110325219)
                  ·
                    refine ⟨99963898967366562165487829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66642599311577708110325219 99963898967366562165487829)
                    ·
                      refine ⟨2342903882047653800753621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99963898967366562165487829 2342903882047653800753621)
                      ·
                        rfl

theorem cell23_4562789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_4562789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562789 prefixEnd_4562789 := by exact prefixLift 4562789
  have htrace : WordTrace (prefixWord ++ tailWord_4562789) baseStart_4562789 baseEnd_4562789 := by
    simpa [prefixWord, tailWord_4562789, baseEnd_4562789] using wordTrace_append hprefix tailTrace_4562789
  have hstable : (prefixWord ++ tailWord_4562789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562789).length < 2 ^ (prefixWord ++ tailWord_4562789).sum := by decide
  have hdescent : baseEnd_4562789 < baseStart_4562789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562796 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 2, 5]
def baseStart_4562796 : Nat := 118140960795 + 4562796 * 2 ^ 59
def prefixEnd_4562796 : Nat := 4983230072969 + 3 ^ 40 * 4562796 * 2
def baseEnd_4562796 : Nat := 780969158804078424455363

theorem tailTrace_4562796 : CollatzResearch.WordTrace tailWord_4562796 prefixEnd_4562796 780969158804078424455363 := by
  unfold tailWord_4562796
  simp only [CollatzResearch.WordTrace]
  refine ⟨83209420988888415180786121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110945894651851220241048161 83209420988888415180786121)
  ·
    refine ⟨62407065741666311385589591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83209420988888415180786121 62407065741666311385589591)
    ·
      refine ⟨93610598612499467078384387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62407065741666311385589591 93610598612499467078384387)
      ·
        refine ⟨140415897918749200617576581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93610598612499467078384387 140415897918749200617576581)
        ·
          refine ⟨26327980859765475115795609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140415897918749200617576581 26327980859765475115795609)
          ·
            refine ⟨19745985644824106336846707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26327980859765475115795609 19745985644824106336846707)
            ·
              refine ⟨29618978467236159505270061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19745985644824106336846707 29618978467236159505270061)
              ·
                refine ⟨11107116925213559814476273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29618978467236159505270061 11107116925213559814476273)
                ·
                  refine ⟨8330337693910169860857205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11107116925213559814476273 8330337693910169860857205)
                  ·
                    refine ⟨780969158804078424455363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8330337693910169860857205 780969158804078424455363)
                    ·
                      rfl

theorem cell23_4562796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_4562796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562796 prefixEnd_4562796 := by exact prefixLift 4562796
  have htrace : WordTrace (prefixWord ++ tailWord_4562796) baseStart_4562796 baseEnd_4562796 := by
    simpa [prefixWord, tailWord_4562796, baseEnd_4562796] using wordTrace_append hprefix tailTrace_4562796
  have hstable : (prefixWord ++ tailWord_4562796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562796).length < 2 ^ (prefixWord ++ tailWord_4562796).sum := by decide
  have hdescent : baseEnd_4562796 < baseStart_4562796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562816 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 4]
def baseStart_4562816 : Nat := 118140960795 + 4562816 * 2 ^ 59
def prefixEnd_4562816 : Nat := 4983230072969 + 3 ^ 40 * 4562816 * 2
def baseEnd_4562816 : Nat := 2342917746025325195115997

theorem tailTrace_4562816 : CollatzResearch.WordTrace tailWord_4562816 prefixEnd_4562816 2342917746025325195115997 := by
  unfold tailWord_4562816
  simp only [CollatzResearch.WordTrace]
  refine ⟨83209785718852186888650151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110946380958469582518200201 83209785718852186888650151)
  ·
    refine ⟨124814678578278280332975227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83209785718852186888650151 124814678578278280332975227)
    ·
      refine ⟨187222017867417420499462841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124814678578278280332975227 187222017867417420499462841)
      ·
        refine ⟨140416513400563065374597131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187222017867417420499462841 140416513400563065374597131)
        ·
          refine ⟨210624770100844598061895697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140416513400563065374597131 210624770100844598061895697)
          ·
            refine ⟨157968577575633448546421773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210624770100844598061895697 157968577575633448546421773)
            ·
              refine ⟨59238216590862543204908165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157968577575633448546421773 59238216590862543204908165)
              ·
                refine ⟨11107165610786726850920281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59238216590862543204908165 11107165610786726850920281)
                ·
                  refine ⟨8330374208090045138190211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11107165610786726850920281 8330374208090045138190211)
                  ·
                    refine ⟨12495561312135067707285317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8330374208090045138190211 12495561312135067707285317)
                    ·
                      refine ⟨2342917746025325195115997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12495561312135067707285317 2342917746025325195115997)
                      ·
                        rfl

theorem cell23_4562816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_4562816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562816 prefixEnd_4562816 := by exact prefixLift 4562816
  have htrace : WordTrace (prefixWord ++ tailWord_4562816) baseStart_4562816 baseEnd_4562816 := by
    simpa [prefixWord, tailWord_4562816, baseEnd_4562816] using wordTrace_append hprefix tailTrace_4562816
  have hstable : (prefixWord ++ tailWord_4562816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562816).length < 2 ^ (prefixWord ++ tailWord_4562816).sum := by decide
  have hdescent : baseEnd_4562816 < baseStart_4562816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562859 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 8]
def baseStart_4562859 : Nat := 118140960795 + 4562859 * 2 ^ 59
def prefixEnd_4562859 : Nat := 4983230072969 + 3 ^ 40 * 4562859 * 2
def baseEnd_4562859 : Nat := 2342939825693468526878299

theorem tailTrace_4562859 : CollatzResearch.WordTrace tailWord_4562859 prefixEnd_4562859 2342939825693468526878299 := by
  unfold tailWord_4562859
  simp only [CollatzResearch.WordTrace]
  refine ⟨166421139776548592121115631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110947426517699061414077087 166421139776548592121115631)
  ·
    refine ⟨249631709664822888181673447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166421139776548592121115631 249631709664822888181673447)
    ·
      refine ⟨374447564497234332272510171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249631709664822888181673447 374447564497234332272510171)
      ·
        refine ⟨561671346745851498408765257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374447564497234332272510171 561671346745851498408765257)
        ·
          refine ⟨421253510059388623806573943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 561671346745851498408765257 421253510059388623806573943)
          ·
            refine ⟨631880265089082935709860915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421253510059388623806573943 631880265089082935709860915)
            ·
              refine ⟨947820397633624403564791373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631880265089082935709860915 947820397633624403564791373)
              ·
                refine ⟨355432649112609151336796765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 947820397633624403564791373 355432649112609151336796765)
                ·
                  refine ⟨133287243417228431751298787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355432649112609151336796765 133287243417228431751298787)
                  ·
                    refine ⟨199930865125842647626948181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 133287243417228431751298787 199930865125842647626948181)
                    ·
                      refine ⟨2342939825693468526878299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 199930865125842647626948181 2342939825693468526878299)
                      ·
                        rfl

theorem cell23_4562859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 8].length) (baseStart_4562859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562859 prefixEnd_4562859 := by exact prefixLift 4562859
  have htrace : WordTrace (prefixWord ++ tailWord_4562859) baseStart_4562859 baseEnd_4562859 := by
    simpa [prefixWord, tailWord_4562859, baseEnd_4562859] using wordTrace_append hprefix tailTrace_4562859
  have hstable : (prefixWord ++ tailWord_4562859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562859).length < 2 ^ (prefixWord ++ tailWord_4562859).sum := by decide
  have hdescent : baseEnd_4562859 < baseStart_4562859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562866 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3]
def baseStart_4562866 : Nat := 118140960795 + 4562866 * 2 ^ 59
def prefixEnd_4562866 : Nat := 4983230072969 + 3 ^ 40 * 4562866 * 2
def baseEnd_4562866 : Nat := 2342943420058049999490767

theorem tailTrace_4562866 : CollatzResearch.WordTrace tailWord_4562866 prefixEnd_4562866 2342943420058049999490767 := by
  unfold tailWord_4562866
  simp only [CollatzResearch.WordTrace]
  refine ⟨41605348771880808079155113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110947596725015488211080301 41605348771880808079155113)
  ·
    refine ⟨31204011578910606059366335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41605348771880808079155113 31204011578910606059366335)
    ·
      refine ⟨46806017368365909089049503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31204011578910606059366335 46806017368365909089049503)
      ·
        refine ⟨70209026052548863633574255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46806017368365909089049503 70209026052548863633574255)
        ·
          refine ⟨105313539078823295450361383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70209026052548863633574255 105313539078823295450361383)
          ·
            refine ⟨157970308618234943175542075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105313539078823295450361383 157970308618234943175542075)
            ·
              refine ⟨236955462927352414763313113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157970308618234943175542075 236955462927352414763313113)
              ·
                refine ⟨177716597195514311072484835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236955462927352414763313113 177716597195514311072484835)
                ·
                  refine ⟨266574895793271466608727253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177716597195514311072484835 266574895793271466608727253)
                  ·
                    refine ⟨6247849120154799998642045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 266574895793271466608727253 6247849120154799998642045)
                    ·
                      refine ⟨2342943420058049999490767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6247849120154799998642045 2342943420058049999490767)
                      ·
                        rfl

theorem cell23_4562866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_4562866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562866 prefixEnd_4562866 := by exact prefixLift 4562866
  have htrace : WordTrace (prefixWord ++ tailWord_4562866) baseStart_4562866 baseEnd_4562866 := by
    simpa [prefixWord, tailWord_4562866, baseEnd_4562866] using wordTrace_append hprefix tailTrace_4562866
  have hstable : (prefixWord ++ tailWord_4562866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562866).length < 2 ^ (prefixWord ++ tailWord_4562866).sum := by decide
  have hdescent : baseEnd_4562866 < baseStart_4562866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562900 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_4562900 : Nat := 118140960795 + 4562900 * 2 ^ 59
def prefixEnd_4562900 : Nat := 4983230072969 + 3 ^ 40 * 4562900 * 2
def baseEnd_4562900 : Nat := 2342960878400302866465611

theorem tailTrace_4562900 : CollatzResearch.WordTrace tailWord_4562900 prefixEnd_4562900 2342960878400302866465611 := by
  unfold tailWord_4562900
  simp only [CollatzResearch.WordTrace]
  refine ⟨83211317584700028061679077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110948423446266704082238769 83211317584700028061679077)
  ·
    refine ⟨15602122047131255261564827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83211317584700028061679077 15602122047131255261564827)
    ·
      refine ⟨23403183070696882892347241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15602122047131255261564827 23403183070696882892347241)
      ·
        refine ⟨17552387303022662169260431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23403183070696882892347241 17552387303022662169260431)
        ·
          refine ⟨26328580954533993253890647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17552387303022662169260431 26328580954533993253890647)
          ·
            refine ⟨39492871431800989880835971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26328580954533993253890647 39492871431800989880835971)
            ·
              refine ⟨59239307147701484821253957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39492871431800989880835971 59239307147701484821253957)
              ·
                refine ⟨11107370090194028403985117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59239307147701484821253957 11107370090194028403985117)
                ·
                  refine ⟨4165263783822760651494419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11107370090194028403985117 4165263783822760651494419)
                  ·
                    refine ⟨6247895675734140977241629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4165263783822760651494419 6247895675734140977241629)
                    ·
                      refine ⟨2342960878400302866465611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6247895675734140977241629 2342960878400302866465611)
                      ·
                        rfl

theorem cell23_4562900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_4562900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562900 prefixEnd_4562900 := by exact prefixLift 4562900
  have htrace : WordTrace (prefixWord ++ tailWord_4562900) baseStart_4562900 baseEnd_4562900 := by
    simpa [prefixWord, tailWord_4562900, baseEnd_4562900] using wordTrace_append hprefix tailTrace_4562900
  have hstable : (prefixWord ++ tailWord_4562900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562900).length < 2 ^ (prefixWord ++ tailWord_4562900).sum := by decide
  have hdescent : baseEnd_4562900 < baseStart_4562900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562903 : List Nat := [1, 1, 3, 2, 1, 1, 6, 2, 1, 5]
def baseStart_4562903 : Nat := 118140960795 + 4562903 * 2 ^ 59
def prefixEnd_4562903 : Nat := 4983230072969 + 3 ^ 40 * 4562903 * 2
def baseEnd_4562903 : Nat := 780987472947422118242699

theorem tailTrace_4562903 : CollatzResearch.WordTrace tailWord_4562903 prefixEnd_4562903 780987472947422118242699 := by
  unfold tailWord_4562903
  simp only [CollatzResearch.WordTrace]
  refine ⟨166422744588389187635717363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110948496392259458423811575 166422744588389187635717363)
  ·
    refine ⟨249634116882583781453576045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166422744588389187635717363 249634116882583781453576045)
    ·
      refine ⟨93612793830968918045091017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249634116882583781453576045 93612793830968918045091017)
      ·
        refine ⟨70209595373226688533818263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93612793830968918045091017 70209595373226688533818263)
        ·
          refine ⟨105314393059840032800727395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70209595373226688533818263 105314393059840032800727395)
          ·
            refine ⟨157971589589760049201091093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105314393059840032800727395 157971589589760049201091093)
            ·
              refine ⟨7404918262020002306301145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 157971589589760049201091093 7404918262020002306301145)
              ·
                refine ⟨5553688696515001729725859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7404918262020002306301145 5553688696515001729725859)
                ·
                  refine ⟨8330533044772502594588789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5553688696515001729725859 8330533044772502594588789)
                  ·
                    refine ⟨780987472947422118242699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8330533044772502594588789 780987472947422118242699)
                    ·
                      rfl

theorem cell23_4562903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_4562903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562903 prefixEnd_4562903 := by exact prefixLift 4562903
  have htrace : WordTrace (prefixWord ++ tailWord_4562903) baseStart_4562903 baseEnd_4562903 := by
    simpa [prefixWord, tailWord_4562903, baseEnd_4562903] using wordTrace_append hprefix tailTrace_4562903
  have hstable : (prefixWord ++ tailWord_4562903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562903).length < 2 ^ (prefixWord ++ tailWord_4562903).sum := by decide
  have hdescent : baseEnd_4562903 < baseStart_4562903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562916 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 3, 6]
def baseStart_4562916 : Nat := 118140960795 + 4562916 * 2 ^ 59
def prefixEnd_4562916 : Nat := 4983230072969 + 3 ^ 40 * 4562916 * 2
def baseEnd_4562916 : Nat := 780989698030258267955179

theorem tailTrace_4562916 : CollatzResearch.WordTrace tailWord_4562916 prefixEnd_4562916 780989698030258267955179 := by
  unfold tailWord_4562916
  simp only [CollatzResearch.WordTrace]
  refine ⟨83211609368671045427970301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110948812491561393903960401 83211609368671045427970301)
  ·
    refine ⟨31204353513251642035488863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83211609368671045427970301 31204353513251642035488863)
    ·
      refine ⟨46806530269877463053233295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31204353513251642035488863 46806530269877463053233295)
      ·
        refine ⟨70209795404816194579849943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46806530269877463053233295 70209795404816194579849943)
        ·
          refine ⟨105314693107224291869774915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70209795404816194579849943 105314693107224291869774915)
          ·
            refine ⟨157972039660836437804662373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105314693107224291869774915 157972039660836437804662373)
            ·
              refine ⟨29619757436406832088374195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157972039660836437804662373 29619757436406832088374195)
              ·
                refine ⟨44429636154610248132561293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29619757436406832088374195 44429636154610248132561293)
                ·
                  refine ⟨16661113557978843049710485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44429636154610248132561293 16661113557978843049710485)
                  ·
                    refine ⟨780989698030258267955179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16661113557978843049710485 780989698030258267955179)
                    ·
                      rfl

theorem cell23_4562916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_4562916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562916 prefixEnd_4562916 := by exact prefixLift 4562916
  have htrace : WordTrace (prefixWord ++ tailWord_4562916) baseStart_4562916 baseEnd_4562916 := by
    simpa [prefixWord, tailWord_4562916, baseEnd_4562916] using wordTrace_append hprefix tailTrace_4562916
  have hstable : (prefixWord ++ tailWord_4562916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562916).length < 2 ^ (prefixWord ++ tailWord_4562916).sum := by decide
  have hdescent : baseEnd_4562916 < baseStart_4562916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562934 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_4562934 : Nat := 118140960795 + 4562934 * 2 ^ 59
def prefixEnd_4562934 : Nat := 4983230072969 + 3 ^ 40 * 4562934 * 2
def baseEnd_4562934 : Nat := 2342978336742555733440455

theorem tailTrace_4562934 : CollatzResearch.WordTrace tailWord_4562934 prefixEnd_4562934 2342978336742555733440455 := by
  unfold tailWord_4562934
  simp only [CollatzResearch.WordTrace]
  refine ⟨10401492203204804995630991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110949250167517919953397237 10401492203204804995630991)
  ·
    refine ⟨15602238304807207493446487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10401492203204804995630991 15602238304807207493446487)
    ·
      refine ⟨23403357457210811240169731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15602238304807207493446487 23403357457210811240169731)
      ·
        refine ⟨35105036185816216860254597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23403357457210811240169731 35105036185816216860254597)
        ·
          refine ⟨6582194284840540661297737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35105036185816216860254597 6582194284840540661297737)
          ·
            refine ⟨4936645713630405495973303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6582194284840540661297737 4936645713630405495973303)
            ·
              refine ⟨7404968570445608243959955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4936645713630405495973303 7404968570445608243959955)
              ·
                refine ⟨11107452855668412365939933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7404968570445608243959955 11107452855668412365939933)
                ·
                  refine ⟨4165294820875654637227475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11107452855668412365939933 4165294820875654637227475)
                  ·
                    refine ⟨6247942231313481955841213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4165294820875654637227475 6247942231313481955841213)
                    ·
                      refine ⟨2342978336742555733440455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6247942231313481955841213 2342978336742555733440455)
                      ·
                        rfl

theorem cell23_4562934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_4562934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562934 prefixEnd_4562934 := by exact prefixLift 4562934
  have htrace : WordTrace (prefixWord ++ tailWord_4562934) baseStart_4562934 baseEnd_4562934 := by
    simpa [prefixWord, tailWord_4562934, baseEnd_4562934] using wordTrace_append hprefix tailTrace_4562934
  have hstable : (prefixWord ++ tailWord_4562934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562934).length < 2 ^ (prefixWord ++ tailWord_4562934).sum := by decide
  have hdescent : baseEnd_4562934 < baseStart_4562934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562936 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 1, 1, 6]
def baseStart_4562936 : Nat := 118140960795 + 4562936 * 2 ^ 59
def prefixEnd_4562936 : Nat := 4983230072969 + 3 ^ 40 * 4562936 * 2
def baseEnd_4562936 : Nat := 2342979363703864725615445

theorem tailTrace_4562936 : CollatzResearch.WordTrace tailWord_4562936 prefixEnd_4562936 2342979363703864725615445 := by
  unfold tailWord_4562936
  simp only [CollatzResearch.WordTrace]
  refine ⟨83211974098634817135834331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110949298798179756181112441 83211974098634817135834331)
  ·
    refine ⟨124817961147952225703751497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83211974098634817135834331 124817961147952225703751497)
    ·
      refine ⟨93613470860964169277813623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124817961147952225703751497 93613470860964169277813623)
      ·
        refine ⟨140420206291446253916720435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93613470860964169277813623 140420206291446253916720435)
        ·
          refine ⟨210630309437169380875080653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140420206291446253916720435 210630309437169380875080653)
          ·
            refine ⟨78986366038938517828155245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210630309437169380875080653 78986366038938517828155245)
            ·
              refine ⟨29619887264601944185558217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78986366038938517828155245 29619887264601944185558217)
              ·
                refine ⟨22214915448451458139168663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29619887264601944185558217 22214915448451458139168663)
                ·
                  refine ⟨33322373172677187208752995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22214915448451458139168663 33322373172677187208752995)
                  ·
                    refine ⟨49983559759015780813129493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33322373172677187208752995 49983559759015780813129493)
                    ·
                      refine ⟨2342979363703864725615445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49983559759015780813129493 2342979363703864725615445)
                      ·
                        rfl

theorem cell23_4562936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_4562936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562936 prefixEnd_4562936 := by exact prefixLift 4562936
  have htrace : WordTrace (prefixWord ++ tailWord_4562936) baseStart_4562936 baseEnd_4562936 := by
    simpa [prefixWord, tailWord_4562936, baseEnd_4562936] using wordTrace_append hprefix tailTrace_4562936
  have hstable : (prefixWord ++ tailWord_4562936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562936).length < 2 ^ (prefixWord ++ tailWord_4562936).sum := by decide
  have hdescent : baseEnd_4562936 < baseStart_4562936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562977 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 1, 1, 5]
def baseStart_4562977 : Nat := 118140960795 + 4562977 * 2 ^ 59
def prefixEnd_4562977 : Nat := 4983230072969 + 3 ^ 40 * 4562977 * 2
def baseEnd_4562977 : Nat := 2343000416410699065202757

theorem tailTrace_4562977 : CollatzResearch.WordTrace tailWord_4562977 prefixEnd_4562977 2343000416410699065202757 := by
  unfold tailWord_4562977
  simp only [CollatzResearch.WordTrace]
  refine ⟨166425443590121098273911185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110950295726747398849274123 166425443590121098273911185)
  ·
    refine ⟨124819082692590823705433389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166425443590121098273911185 124819082692590823705433389)
    ·
      refine ⟨46807156009721558889537521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124819082692590823705433389 46807156009721558889537521)
      ·
        refine ⟨35105367007291169167153141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46807156009721558889537521 35105367007291169167153141)
        ·
          refine ⟨3291128156933547109420607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35105367007291169167153141 3291128156933547109420607)
          ·
            refine ⟨4936692235400320664130911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3291128156933547109420607 4936692235400320664130911)
            ·
              refine ⟨7405038353100480996196367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4936692235400320664130911 7405038353100480996196367)
              ·
                refine ⟨11107557529650721494294551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7405038353100480996196367 11107557529650721494294551)
                ·
                  refine ⟨16661336294476082241441827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11107557529650721494294551 16661336294476082241441827)
                  ·
                    refine ⟨24992004441714123362162741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16661336294476082241441827 24992004441714123362162741)
                    ·
                      refine ⟨2343000416410699065202757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24992004441714123362162741 2343000416410699065202757)
                      ·
                        rfl

theorem cell23_4562977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_4562977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562977 prefixEnd_4562977 := by exact prefixLift 4562977
  have htrace : WordTrace (prefixWord ++ tailWord_4562977) baseStart_4562977 baseEnd_4562977 := by
    simpa [prefixWord, tailWord_4562977, baseEnd_4562977] using wordTrace_append hprefix tailTrace_4562977
  have hstable : (prefixWord ++ tailWord_4562977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562977).length < 2 ^ (prefixWord ++ tailWord_4562977).sum := by decide
  have hdescent : baseEnd_4562977 < baseStart_4562977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4562984 : List Nat := [2, 1, 5, 3, 1, 1, 2, 2, 2, 4]
def baseStart_4562984 : Nat := 118140960795 + 4562984 * 2 ^ 59
def prefixEnd_4562984 : Nat := 4983230072969 + 3 ^ 40 * 4562984 * 2
def baseEnd_4562984 : Nat := 781001336925093512605075

theorem tailTrace_4562984 : CollatzResearch.WordTrace tailWord_4562984 prefixEnd_4562984 781001336925093512605075 := by
  unfold tailWord_4562984
  simp only [CollatzResearch.WordTrace]
  refine ⟨83212849450547869234708003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110950465934063825646277337 83212849450547869234708003)
  ·
    refine ⟨124819274175821803852062005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83212849450547869234708003 124819274175821803852062005)
    ·
      refine ⟨11701806953983294111130813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124819274175821803852062005 11701806953983294111130813)
      ·
        refine ⟨4388177607743735291674055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11701806953983294111130813 4388177607743735291674055)
        ·
          refine ⟨6582266411615602937511083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4388177607743735291674055 6582266411615602937511083)
          ·
            refine ⟨9873399617423404406266625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6582266411615602937511083 9873399617423404406266625)
            ·
              refine ⟨7405049713067553304699969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9873399617423404406266625 7405049713067553304699969)
              ·
                refine ⟨5553787284800664978524977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7405049713067553304699969 5553787284800664978524977)
                ·
                  refine ⟨4165340463600498733893733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5553787284800664978524977 4165340463600498733893733)
                  ·
                    refine ⟨781001336925093512605075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4165340463600498733893733 781001336925093512605075)
                    ·
                      rfl

theorem cell23_4562984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_4562984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4562984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4562984 prefixEnd_4562984 := by exact prefixLift 4562984
  have htrace : WordTrace (prefixWord ++ tailWord_4562984) baseStart_4562984 baseEnd_4562984 := by
    simpa [prefixWord, tailWord_4562984, baseEnd_4562984] using wordTrace_append hprefix tailTrace_4562984
  have hstable : (prefixWord ++ tailWord_4562984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4562984).length < 2 ^ (prefixWord ++ tailWord_4562984).sum := by decide
  have hdescent : baseEnd_4562984 < baseStart_4562984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4562984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563043 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 4]
def baseStart_4563043 : Nat := 118140960795 + 4563043 * 2 ^ 59
def prefixEnd_4563043 : Nat := 4983230072969 + 3 ^ 40 * 4563043 * 2
def baseEnd_4563043 : Nat := 2343034306133895806977453

theorem tailTrace_4563043 : CollatzResearch.WordTrace tailWord_4563043 prefixEnd_4563043 2343034306133895806977453 := by
  unfold tailWord_4563043
  simp only [CollatzResearch.WordTrace]
  refine ⟨166427850807881991545813783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110951900538587994363875855 166427850807881991545813783)
  ·
    refine ⟨249641776211822987318720675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166427850807881991545813783 249641776211822987318720675)
    ·
      refine ⟨374462664317734480978081013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249641776211822987318720675 374462664317734480978081013)
      ·
        refine ⟨35105874779787607591695095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 374462664317734480978081013 35105874779787607591695095)
        ·
          refine ⟨52658812169681411387542643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35105874779787607591695095 52658812169681411387542643)
          ·
            refine ⟨78988218254522117081313965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52658812169681411387542643 78988218254522117081313965)
            ·
              refine ⟨29620581845445793905492737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78988218254522117081313965 29620581845445793905492737)
              ·
                refine ⟨22215436384084345429119553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29620581845445793905492737 22215436384084345429119553)
                ·
                  refine ⟨16661577288063259071839665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22215436384084345429119553 16661577288063259071839665)
                  ·
                    refine ⟨12496182966047444303879749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16661577288063259071839665 12496182966047444303879749)
                    ·
                      refine ⟨2343034306133895806977453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12496182966047444303879749 2343034306133895806977453)
                      ·
                        rfl

theorem cell23_4563043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_4563043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563043 prefixEnd_4563043 := by exact prefixLift 4563043
  have htrace : WordTrace (prefixWord ++ tailWord_4563043) baseStart_4563043 baseEnd_4563043 := by
    simpa [prefixWord, tailWord_4563043, baseEnd_4563043] using wordTrace_append hprefix tailTrace_4563043
  have hstable : (prefixWord ++ tailWord_4563043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563043).length < 2 ^ (prefixWord ++ tailWord_4563043).sum := by decide
  have hdescent : baseEnd_4563043 < baseStart_4563043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563047 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 4, 2, 2]
def baseStart_4563047 : Nat := 118140960795 + 4563047 * 2 ^ 59
def prefixEnd_4563047 : Nat := 4983230072969 + 3 ^ 40 * 4563047 * 2
def baseEnd_4563047 : Nat := 2343036360056513791327435

theorem tailTrace_4563047 : CollatzResearch.WordTrace tailWord_4563047 prefixEnd_4563047 2343036360056513791327435 := by
  unfold tailWord_4563047
  simp only [CollatzResearch.WordTrace]
  refine ⟨166427996699867500228959395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110951997799911666819306263 166427996699867500228959395)
  ·
    refine ⟨249641995049801250343439093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166427996699867500228959395 249641995049801250343439093)
    ·
      refine ⟨23403937035918867219697415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 249641995049801250343439093 23403937035918867219697415)
      ·
        refine ⟨35105905553878300829546123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23403937035918867219697415 35105905553878300829546123)
        ·
          refine ⟨52658858330817451244319185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35105905553878300829546123 52658858330817451244319185)
          ·
            refine ⟨39494143748113088433239389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52658858330817451244319185 39494143748113088433239389)
            ·
              refine ⟨14810303905542408162464771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39494143748113088433239389 14810303905542408162464771)
              ·
                refine ⟨22215455858313612243697157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14810303905542408162464771 22215455858313612243697157)
                ·
                  refine ⟨4165397973433802295693217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22215455858313612243697157 4165397973433802295693217)
                  ·
                    refine ⟨3124048480075351721769913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4165397973433802295693217 3124048480075351721769913)
                    ·
                      refine ⟨2343036360056513791327435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3124048480075351721769913 2343036360056513791327435)
                      ·
                        rfl

theorem cell23_4563047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_4563047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563047 prefixEnd_4563047 := by exact prefixLift 4563047
  have htrace : WordTrace (prefixWord ++ tailWord_4563047) baseStart_4563047 baseEnd_4563047 := by
    simpa [prefixWord, tailWord_4563047, baseEnd_4563047] using wordTrace_append hprefix tailTrace_4563047
  have hstable : (prefixWord ++ tailWord_4563047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563047).length < 2 ^ (prefixWord ++ tailWord_4563047).sum := by decide
  have hdescent : baseEnd_4563047 < baseStart_4563047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563093 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_4563093 : Nat := 118140960795 + 4563093 * 2 ^ 59
def prefixEnd_4563093 : Nat := 4983230072969 + 3 ^ 40 * 4563093 * 2
def baseEnd_4563093 : Nat := 2343059980166620611352223

theorem tailTrace_4563093 : CollatzResearch.WordTrace tailWord_4563093 prefixEnd_4563093 2343059980166620611352223 := by
  unfold tailWord_4563093
  simp only [CollatzResearch.WordTrace]
  refine ⟨166429674457700850085133933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110953116305133900056755955 166429674457700850085133933)
  ·
    refine ⟨62411127921637818781925225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166429674457700850085133933 62411127921637818781925225)
    ·
      refine ⟨46808345941228364086443919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62411127921637818781925225 46808345941228364086443919)
      ·
        refine ⟨70212518911842546129665879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46808345941228364086443919 70212518911842546129665879)
        ·
          refine ⟨105318778367763819194498819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70212518911842546129665879 105318778367763819194498819)
          ·
            refine ⟨157978167551645728791748229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105318778367763819194498819 157978167551645728791748229)
            ·
              refine ⟨29620906415933574148452793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157978167551645728791748229 29620906415933574148452793)
              ·
                refine ⟨22215679811950180611339595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29620906415933574148452793 22215679811950180611339595)
                ·
                  refine ⟨33323519717925270917009393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22215679811950180611339595 33323519717925270917009393)
                  ·
                    refine ⟨24992639788443953187757045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33323519717925270917009393 24992639788443953187757045)
                    ·
                      refine ⟨2343059980166620611352223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24992639788443953187757045 2343059980166620611352223)
                      ·
                        rfl

theorem cell23_4563093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_4563093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563093 prefixEnd_4563093 := by exact prefixLift 4563093
  have htrace : WordTrace (prefixWord ++ tailWord_4563093) baseStart_4563093 baseEnd_4563093 := by
    simpa [prefixWord, tailWord_4563093, baseEnd_4563093] using wordTrace_append hprefix tailTrace_4563093
  have hstable : (prefixWord ++ tailWord_4563093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563093).length < 2 ^ (prefixWord ++ tailWord_4563093).sum := by decide
  have hdescent : baseEnd_4563093 < baseStart_4563093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563100 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 2, 5]
def baseStart_4563100 : Nat := 118140960795 + 4563100 * 2 ^ 59
def prefixEnd_4563100 : Nat := 4983230072969 + 3 ^ 40 * 4563100 * 2
def baseEnd_4563100 : Nat := 781021191510400694654897

theorem tailTrace_4563100 : CollatzResearch.WordTrace tailWord_4563100 prefixEnd_4563100 781021191510400694654897 := by
  unfold tailWord_4563100
  simp only [CollatzResearch.WordTrace]
  refine ⟨83214964884337745140319377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110953286512450326853759169 83214964884337745140319377)
  ·
    refine ⟨62411223663253308855239533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83214964884337745140319377 62411223663253308855239533)
    ·
      refine ⟨23404208873719990820714825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62411223663253308855239533 23404208873719990820714825)
      ·
        refine ⟨17553156655289993115536119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23404208873719990820714825 17553156655289993115536119)
        ·
          refine ⟨26329734982934989673304179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17553156655289993115536119 26329734982934989673304179)
          ·
            refine ⟨39494602474402484509956269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26329734982934989673304179 39494602474402484509956269)
            ·
              refine ⟨14810475927900931691233601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39494602474402484509956269 14810475927900931691233601)
              ·
                refine ⟨11107856945925698768425201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14810475927900931691233601 11107856945925698768425201)
                ·
                  refine ⟨8330892709444274076318901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11107856945925698768425201 8330892709444274076318901)
                  ·
                    refine ⟨781021191510400694654897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8330892709444274076318901 781021191510400694654897)
                    ·
                      rfl

theorem cell23_4563100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_4563100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563100 prefixEnd_4563100 := by exact prefixLift 4563100
  have htrace : WordTrace (prefixWord ++ tailWord_4563100) baseStart_4563100 baseEnd_4563100 := by
    simpa [prefixWord, tailWord_4563100, baseEnd_4563100] using wordTrace_append hprefix tailTrace_4563100
  have hstable : (prefixWord ++ tailWord_4563100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563100).length < 2 ^ (prefixWord ++ tailWord_4563100).sum := by decide
  have hdescent : baseEnd_4563100 < baseStart_4563100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563130 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 3, 4]
def baseStart_4563130 : Nat := 118140960795 + 4563130 * 2 ^ 59
def prefixEnd_4563130 : Nat := 4983230072969 + 3 ^ 40 * 4563130 * 2
def baseEnd_4563130 : Nat := 781026326316945655529851

theorem tailTrace_4563130 : CollatzResearch.WordTrace tailWord_4563130 prefixEnd_4563130 781026326316945655529851 := by
  unfold tailWord_4563130
  simp only [CollatzResearch.WordTrace]
  refine ⟨41607755989641701351057711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110954015972377870269487229 41607755989641701351057711)
  ·
    refine ⟨62411633984462552026586567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41607755989641701351057711 62411633984462552026586567)
    ·
      refine ⟨93617450976693828039879851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62411633984462552026586567 93617450976693828039879851)
      ·
        refine ⟨140426176465040742059819777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93617450976693828039879851 140426176465040742059819777)
        ·
          refine ⟨105319632348780556544864833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140426176465040742059819777 105319632348780556544864833)
          ·
            refine ⟨78989724261585417408648625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105319632348780556544864833 78989724261585417408648625)
            ·
              refine ⟨59242293196189063056486469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78989724261585417408648625 59242293196189063056486469)
              ·
                refine ⟨11107929974285449323091213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59242293196189063056486469 11107929974285449323091213)
                ·
                  refine ⟨4165473740357043496159205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11107929974285449323091213 4165473740357043496159205)
                  ·
                    refine ⟨781026326316945655529851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4165473740357043496159205 781026326316945655529851)
                    ·
                      rfl

theorem cell23_4563130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_4563130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563130 prefixEnd_4563130 := by exact prefixLift 4563130
  have htrace : WordTrace (prefixWord ++ tailWord_4563130) baseStart_4563130 baseEnd_4563130 := by
    simpa [prefixWord, tailWord_4563130, baseEnd_4563130] using wordTrace_append hprefix tailTrace_4563130
  have hstable : (prefixWord ++ tailWord_4563130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563130).length < 2 ^ (prefixWord ++ tailWord_4563130).sum := by decide
  have hdescent : baseEnd_4563130 < baseStart_4563130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563133 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_4563133 : Nat := 118140960795 + 4563133 * 2 ^ 59
def prefixEnd_4563133 : Nat := 4983230072969 + 3 ^ 40 * 4563133 * 2
def baseEnd_4563133 : Nat := 2343080519392800454852039

theorem tailTrace_4563133 : CollatzResearch.WordTrace tailWord_4563133 prefixEnd_4563133 2343080519392800454852039 := by
  unfold tailWord_4563133
  simp only [CollatzResearch.WordTrace]
  refine ⟨166431133377555936916590053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110954088918370624611060035 166431133377555936916590053)
  ·
    refine ⟨31205837508291738171860635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166431133377555936916590053 31205837508291738171860635)
    ·
      refine ⟨46808756262437607257790953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31205837508291738171860635 46808756262437607257790953)
      ·
        refine ⟨35106567196828205443343215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46808756262437607257790953 35106567196828205443343215)
        ·
          refine ⟨52659850795242308165014823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35106567196828205443343215 52659850795242308165014823)
          ·
            refine ⟨78989776192863462247522235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52659850795242308165014823 78989776192863462247522235)
            ·
              refine ⟨118484664289295193371283353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78989776192863462247522235 118484664289295193371283353)
              ·
                refine ⟨88863498216971395028462515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118484664289295193371283353 88863498216971395028462515)
                ·
                  refine ⟨133295247325457092542693773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88863498216971395028462515 133295247325457092542693773)
                  ·
                    refine ⟨49985717747046409703510165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133295247325457092542693773 49985717747046409703510165)
                    ·
                      refine ⟨2343080519392800454852039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49985717747046409703510165 2343080519392800454852039)
                      ·
                        rfl

theorem cell23_4563133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_4563133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563133 prefixEnd_4563133 := by exact prefixLift 4563133
  have htrace : WordTrace (prefixWord ++ tailWord_4563133) baseStart_4563133 baseEnd_4563133 := by
    simpa [prefixWord, tailWord_4563133, baseEnd_4563133] using wordTrace_append hprefix tailTrace_4563133
  have hstable : (prefixWord ++ tailWord_4563133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563133).length < 2 ^ (prefixWord ++ tailWord_4563133).sum := by decide
  have hdescent : baseEnd_4563133 < baseStart_4563133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563147 : List Nat := [1, 1, 1, 1, 3, 2, 4, 5, 1, 4]
def baseStart_4563147 : Nat := 118140960795 + 4563147 * 2 ^ 59
def prefixEnd_4563147 : Nat := 4983230072969 + 3 ^ 40 * 4563147 * 2
def baseEnd_4563147 : Nat := 781029236040654466692325

theorem tailTrace_4563147 : CollatzResearch.WordTrace tailWord_4563147 prefixEnd_4563147 781029236040654466692325 := by
  unfold tailWord_4563147
  simp only [CollatzResearch.WordTrace]
  refine ⟨166431643999505217307599695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110954429333003478205066463 166431643999505217307599695)
  ·
    refine ⟨249647465999257825961399543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166431643999505217307599695 249647465999257825961399543)
    ·
      refine ⟨374471198998886738942099315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249647465999257825961399543 374471198998886738942099315)
      ·
        refine ⟨561706798498330108413148973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374471198998886738942099315 561706798498330108413148973)
        ·
          refine ⟨210640049436873790654930865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 561706798498330108413148973 210640049436873790654930865)
          ·
            refine ⟨157980037077655342991198149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210640049436873790654930865 157980037077655342991198149)
            ·
              refine ⟨29621256952060376810849653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157980037077655342991198149 29621256952060376810849653)
              ·
                refine ⟨2776992839255660326017155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29621256952060376810849653 2776992839255660326017155)
                ·
                  refine ⟨4165489258883490489025733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2776992839255660326017155 4165489258883490489025733)
                  ·
                    refine ⟨781029236040654466692325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4165489258883490489025733 781029236040654466692325)
                    ·
                      rfl

theorem cell23_4563147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 1, 4].length) (baseStart_4563147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563147 prefixEnd_4563147 := by exact prefixLift 4563147
  have htrace : WordTrace (prefixWord ++ tailWord_4563147) baseStart_4563147 baseEnd_4563147 := by
    simpa [prefixWord, tailWord_4563147, baseEnd_4563147] using wordTrace_append hprefix tailTrace_4563147
  have hstable : (prefixWord ++ tailWord_4563147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563147).length < 2 ^ (prefixWord ++ tailWord_4563147).sum := by decide
  have hdescent : baseEnd_4563147 < baseStart_4563147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563160 : List Nat := [2, 1, 2, 2, 4, 1, 1, 4, 6]
def baseStart_4563160 : Nat := 118140960795 + 4563160 * 2 ^ 59
def prefixEnd_4563160 : Nat := 4983230072969 + 3 ^ 40 * 4563160 * 2
def baseEnd_4563160 : Nat := 260343820374496872134935

theorem tailTrace_4563160 : CollatzResearch.WordTrace tailWord_4563160 prefixEnd_4563160 260343820374496872134935 := by
  unfold tailWord_4563160
  simp only [CollatzResearch.WordTrace]
  refine ⟨83216059074229060263911467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110954745432305413685215289 83216059074229060263911467)
  ·
    refine ⟨124824088611343590395867201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83216059074229060263911467 124824088611343590395867201)
    ·
      refine ⟨93618066458507692796900401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124824088611343590395867201 93618066458507692796900401)
      ·
        refine ⟨70213549843880769597675301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93618066458507692796900401 70213549843880769597675301)
        ·
          refine ⟨13165040595727644299564119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70213549843880769597675301 13165040595727644299564119)
          ·
            refine ⟨19747560893591466449346179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13165040595727644299564119 19747560893591466449346179)
            ·
              refine ⟨29621341340387199674019269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19747560893591466449346179 29621341340387199674019269)
              ·
                refine ⟨5554001501322599938878613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29621341340387199674019269 5554001501322599938878613)
                ·
                  refine ⟨260343820374496872134935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5554001501322599938878613 260343820374496872134935)
                  ·
                    rfl

theorem cell23_4563160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 6].length) (baseStart_4563160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563160 prefixEnd_4563160 := by exact prefixLift 4563160
  have htrace : WordTrace (prefixWord ++ tailWord_4563160) baseStart_4563160 baseEnd_4563160 := by
    simpa [prefixWord, tailWord_4563160, baseEnd_4563160] using wordTrace_append hprefix tailTrace_4563160
  have hstable : (prefixWord ++ tailWord_4563160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563160).length < 2 ^ (prefixWord ++ tailWord_4563160).sum := by decide
  have hdescent : baseEnd_4563160 < baseStart_4563160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563187 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 3, 1, 3]
def baseStart_4563187 : Nat := 118140960795 + 4563187 * 2 ^ 59
def prefixEnd_4563187 : Nat := 4983230072969 + 3 ^ 40 * 4563187 * 2
def baseEnd_4563187 : Nat := 2343108247348143243576791

theorem tailTrace_4563187 : CollatzResearch.WordTrace tailWord_4563187 prefixEnd_4563187 2343108247348143243576791 := by
  unfold tailWord_4563187
  simp only [CollatzResearch.WordTrace]
  refine ⟨166433102919360304139055815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110955401946240202759370543 166433102919360304139055815)
  ·
    refine ⟨249649654379040456208583723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166433102919360304139055815 249649654379040456208583723)
    ·
      refine ⟨374474481568560684312875585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249649654379040456208583723 374474481568560684312875585)
      ·
        refine ⟨280855861176420513234656689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374474481568560684312875585 280855861176420513234656689)
        ·
          refine ⟨210641895882315384925992517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280855861176420513234656689 210641895882315384925992517)
          ·
            refine ⟨39495355477934134673623597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210641895882315384925992517 39495355477934134673623597)
            ·
              refine ⟨14810758304225300502608849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39495355477934134673623597 14810758304225300502608849)
              ·
                refine ⟨11108068728168975376956637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14810758304225300502608849 11108068728168975376956637)
                ·
                  refine ⟨4165525773063365766358739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11108068728168975376956637 4165525773063365766358739)
                  ·
                    refine ⟨6248288659595048649538109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4165525773063365766358739 6248288659595048649538109)
                    ·
                      refine ⟨2343108247348143243576791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6248288659595048649538109 2343108247348143243576791)
                      ·
                        rfl

theorem cell23_4563187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 1, 3].length) (baseStart_4563187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563187 prefixEnd_4563187 := by exact prefixLift 4563187
  have htrace : WordTrace (prefixWord ++ tailWord_4563187) baseStart_4563187 baseEnd_4563187 := by
    simpa [prefixWord, tailWord_4563187, baseEnd_4563187] using wordTrace_append hprefix tailTrace_4563187
  have hstable : (prefixWord ++ tailWord_4563187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563187).length < 2 ^ (prefixWord ++ tailWord_4563187).sum := by decide
  have hdescent : baseEnd_4563187 < baseStart_4563187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563244 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 3, 2, 2]
def baseStart_4563244 : Nat := 118140960795 + 4563244 * 2 ^ 59
def prefixEnd_4563244 : Nat := 4983230072969 + 3 ^ 40 * 4563244 * 2
def baseEnd_4563244 : Nat := 2343137515745449520564029

theorem tailTrace_4563244 : CollatzResearch.WordTrace tailWord_4563244 prefixEnd_4563244 2343137515745449520564029 := by
  unfold tailWord_4563244
  simp only [CollatzResearch.WordTrace]
  refine ⟨83217590940076901436940393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110956787920102535249253857 83217590940076901436940393)
  ·
    refine ⟨62413193205057676077705295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83217590940076901436940393 62413193205057676077705295)
    ·
      refine ⟨93619789807586514116557943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62413193205057676077705295 93619789807586514116557943)
      ·
        refine ⟨140429684711379771174836915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93619789807586514116557943 140429684711379771174836915)
        ·
          refine ⟨210644527067069656762255373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140429684711379771174836915 210644527067069656762255373)
          ·
            refine ⟨78991697650151121285845765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210644527067069656762255373 78991697650151121285845765)
            ·
              refine ⟨14810943309403335241096081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78991697650151121285845765 14810943309403335241096081)
              ·
                refine ⟨11108207482052501430822061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14810943309403335241096081 11108207482052501430822061)
                ·
                  refine ⟨4165577805769688036558273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11108207482052501430822061 4165577805769688036558273)
                  ·
                    refine ⟨3124183354327266027418705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4165577805769688036558273 3124183354327266027418705)
                    ·
                      refine ⟨2343137515745449520564029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3124183354327266027418705 2343137515745449520564029)
                      ·
                        rfl

theorem cell23_4563244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 2, 2].length) (baseStart_4563244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563244 prefixEnd_4563244 := by exact prefixLift 4563244
  have htrace : WordTrace (prefixWord ++ tailWord_4563244) baseStart_4563244 baseEnd_4563244 := by
    simpa [prefixWord, tailWord_4563244, baseEnd_4563244] using wordTrace_append hprefix tailTrace_4563244
  have hstable : (prefixWord ++ tailWord_4563244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563244).length < 2 ^ (prefixWord ++ tailWord_4563244).sum := by decide
  have hdescent : baseEnd_4563244 < baseStart_4563244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563247 : List Nat := [1, 1, 2, 1, 2, 1, 5, 4, 1, 2, 3]
def baseStart_4563247 : Nat := 118140960795 + 4563247 * 2 ^ 59
def prefixEnd_4563247 : Nat := 4983230072969 + 3 ^ 40 * 4563247 * 2
def baseEnd_4563247 : Nat := 2343139056187413008826515

theorem tailTrace_4563247 : CollatzResearch.WordTrace tailWord_4563247 prefixEnd_4563247 2343139056187413008826515 := by
  unfold tailWord_4563247
  simp only [CollatzResearch.WordTrace]
  refine ⟨166435291299142934386239995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110956860866095289590826663 166435291299142934386239995)
  ·
    refine ⟨249652936948714401579359993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166435291299142934386239995 249652936948714401579359993)
    ·
      refine ⟨187239702711535801184519995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249652936948714401579359993 187239702711535801184519995)
      ·
        refine ⟨280859554067303701776779993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187239702711535801184519995 280859554067303701776779993)
        ·
          refine ⟨210644665550477776332584995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280859554067303701776779993 210644665550477776332584995)
          ·
            refine ⟨315966998325716664498877493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210644665550477776332584995 315966998325716664498877493)
            ·
              refine ⟨29621906093035937296769765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 315966998325716664498877493 29621906093035937296769765)
              ·
                refine ⟨5554107392444238243144331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29621906093035937296769765 5554107392444238243144331)
                ·
                  refine ⟨8331161088666357364716497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5554107392444238243144331 8331161088666357364716497)
                  ·
                    refine ⟨6248370816499768023537373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8331161088666357364716497 6248370816499768023537373)
                    ·
                      refine ⟨2343139056187413008826515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6248370816499768023537373 2343139056187413008826515)
                      ·
                        rfl

theorem cell23_4563247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 2, 3].length) (baseStart_4563247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563247 prefixEnd_4563247 := by exact prefixLift 4563247
  have htrace : WordTrace (prefixWord ++ tailWord_4563247) baseStart_4563247 baseEnd_4563247 := by
    simpa [prefixWord, tailWord_4563247, baseEnd_4563247] using wordTrace_append hprefix tailTrace_4563247
  have hstable : (prefixWord ++ tailWord_4563247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563247).length < 2 ^ (prefixWord ++ tailWord_4563247).sum := by decide
  have hdescent : baseEnd_4563247 < baseStart_4563247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563337 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 2, 4, 3]
def baseStart_4563337 : Nat := 118140960795 + 4563337 * 2 ^ 59
def prefixEnd_4563337 : Nat := 4983230072969 + 3 ^ 40 * 4563337 * 2
def baseEnd_4563337 : Nat := 2343185269446317656701101

theorem tailTrace_4563337 : CollatzResearch.WordTrace tailWord_4563337 prefixEnd_4563337 2343185269446317656701101 := by
  unfold tailWord_4563337
  simp only [CollatzResearch.WordTrace]
  refine ⟨166438573868816879757016265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110959049245877919838010843 166438573868816879757016265)
  ·
    refine ⟨124828930401612659817762199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166438573868816879757016265 124828930401612659817762199)
    ·
      refine ⟨187243395602418989726643299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124828930401612659817762199 187243395602418989726643299)
      ·
        refine ⟨280865093403628484589964949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187243395602418989726643299 280865093403628484589964949)
        ·
          refine ⟨13165551253295085215154607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 280865093403628484589964949 13165551253295085215154607)
          ·
            refine ⟨19748326879942627822731911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13165551253295085215154607 19748326879942627822731911)
            ·
              refine ⟨29622490319913941734097867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19748326879942627822731911 29622490319913941734097867)
              ·
                refine ⟨44433735479870912601146801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29622490319913941734097867 44433735479870912601146801)
                ·
                  refine ⟨33325301609903184450860101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44433735479870912601146801 33325301609903184450860101)
                  ·
                    refine ⟨6248494051856847084536269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33325301609903184450860101 6248494051856847084536269)
                    ·
                      refine ⟨2343185269446317656701101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6248494051856847084536269 2343185269446317656701101)
                      ·
                        rfl

theorem cell23_4563337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 4, 3].length) (baseStart_4563337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563337 prefixEnd_4563337 := by exact prefixLift 4563337
  have htrace : WordTrace (prefixWord ++ tailWord_4563337) baseStart_4563337 baseEnd_4563337 := by
    simpa [prefixWord, tailWord_4563337, baseEnd_4563337] using wordTrace_append hprefix tailTrace_4563337
  have hstable : (prefixWord ++ tailWord_4563337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563337).length < 2 ^ (prefixWord ++ tailWord_4563337).sum := by decide
  have hdescent : baseEnd_4563337 < baseStart_4563337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563351 : List Nat := [1, 1, 3, 3, 1, 1, 4, 3, 2, 2, 2]
def baseStart_4563351 : Nat := 118140960795 + 4563351 * 2 ^ 59
def prefixEnd_4563351 : Nat := 4983230072969 + 3 ^ 40 * 4563351 * 2
def baseEnd_4563351 : Nat := 2343192458175480601926037

theorem tailTrace_4563351 : CollatzResearch.WordTrace tailWord_4563351 prefixEnd_4563351 2343192458175480601926037 := by
  unfold tailWord_4563351
  simp only [CollatzResearch.WordTrace]
  refine ⟨166439084490766160148025907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110959389660510773432017271 166439084490766160148025907)
  ·
    refine ⟨249658626736149240222038861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166439084490766160148025907 249658626736149240222038861)
    ·
      refine ⟨93621985026055965083264573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249658626736149240222038861 93621985026055965083264573)
      ·
        refine ⟨35108244384770986906224215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93621985026055965083264573 35108244384770986906224215)
        ·
          refine ⟨52662366577156480359336323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35108244384770986906224215 52662366577156480359336323)
          ·
            refine ⟨78993549865734720539004485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52662366577156480359336323 78993549865734720539004485)
            ·
              refine ⟨14811290599825260101063341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78993549865734720539004485 14811290599825260101063341)
              ·
                refine ⟨5554233974934472537898753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14811290599825260101063341 5554233974934472537898753)
                ·
                  refine ⟨4165675481200854403424065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5554233974934472537898753 4165675481200854403424065)
                  ·
                    refine ⟨3124256610900640802568049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4165675481200854403424065 3124256610900640802568049)
                    ·
                      refine ⟨2343192458175480601926037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3124256610900640802568049 2343192458175480601926037)
                      ·
                        rfl

theorem cell23_4563351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_4563351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563351 prefixEnd_4563351 := by exact prefixLift 4563351
  have htrace : WordTrace (prefixWord ++ tailWord_4563351) baseStart_4563351 baseEnd_4563351 := by
    simpa [prefixWord, tailWord_4563351, baseEnd_4563351] using wordTrace_append hprefix tailTrace_4563351
  have hstable : (prefixWord ++ tailWord_4563351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563351).length < 2 ^ (prefixWord ++ tailWord_4563351).sum := by decide
  have hdescent : baseEnd_4563351 < baseStart_4563351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563502 : List Nat := [4, 1, 3, 1, 3, 2, 2, 2, 1, 4]
def baseStart_4563502 : Nat := 118140960795 + 4563502 * 2 ^ 59
def prefixEnd_4563502 : Nat := 4983230072969 + 3 ^ 40 * 4563502 * 2
def baseEnd_4563502 : Nat := 781089997918103170379281

theorem tailTrace_4563502 : CollatzResearch.WordTrace tailWord_4563502 prefixEnd_4563502 781089997918103170379281 := by
  unfold tailWord_4563502
  simp only [CollatzResearch.WordTrace]
  refine ⟨20805573989152389117096595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110963061275479408624515173 20805573989152389117096595)
  ·
    refine ⟨31208360983728583675644893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20805573989152389117096595 31208360983728583675644893)
    ·
      refine ⟨11703135368898218878366835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31208360983728583675644893 11703135368898218878366835)
      ·
        refine ⟨17554703053347328317550253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11703135368898218878366835 17554703053347328317550253)
        ·
          refine ⟨6583013645005248119081345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17554703053347328317550253 6583013645005248119081345)
          ·
            refine ⟨4937260233753936089311009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6583013645005248119081345 4937260233753936089311009)
            ·
              refine ⟨3702945175315452066983257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4937260233753936089311009 3702945175315452066983257)
              ·
                refine ⟨2777208881486589050237443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3702945175315452066983257 2777208881486589050237443)
                ·
                  refine ⟨4165813322229883575356165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2777208881486589050237443 4165813322229883575356165)
                  ·
                    refine ⟨781089997918103170379281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4165813322229883575356165 781089997918103170379281)
                    ·
                      rfl

theorem cell23_4563502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_4563502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563502 prefixEnd_4563502 := by exact prefixLift 4563502
  have htrace : WordTrace (prefixWord ++ tailWord_4563502) baseStart_4563502 baseEnd_4563502 := by
    simpa [prefixWord, tailWord_4563502, baseEnd_4563502] using wordTrace_append hprefix tailTrace_4563502
  have hstable : (prefixWord ++ tailWord_4563502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563502).length < 2 ^ (prefixWord ++ tailWord_4563502).sum := by decide
  have hdescent : baseEnd_4563502 < baseStart_4563502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563507 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 3, 6]
def baseStart_4563507 : Nat := 118140960795 + 4563507 * 2 ^ 59
def prefixEnd_4563507 : Nat := 4983230072969 + 3 ^ 40 * 4563507 * 2
def baseEnd_4563507 : Nat := 781090853719193997191773

theorem tailTrace_4563507 : CollatzResearch.WordTrace tailWord_4563507 prefixEnd_4563507 781090853719193997191773 := by
  unfold tailWord_4563507
  simp only [CollatzResearch.WordTrace]
  refine ⟨166444774278200998790704775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110963182852133999193803183 166444774278200998790704775)
  ·
    refine ⟨249667161417301498186057163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166444774278200998790704775 249667161417301498186057163)
    ·
      refine ⟨374500742125952247279085745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249667161417301498186057163 374500742125952247279085745)
      ·
        refine ⟨280875556594464185459314309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374500742125952247279085745 280875556594464185459314309)
        ·
          refine ⟨52664166861462034773621433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 280875556594464185459314309 52664166861462034773621433)
          ·
            refine ⟨39498125146096526080216075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52664166861462034773621433 39498125146096526080216075)
            ·
              refine ⟨59247187719144789120324113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39498125146096526080216075 59247187719144789120324113)
              ·
                refine ⟨44435390789358591840243085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59247187719144789120324113 44435390789358591840243085)
                ·
                  refine ⟨16663271546009471940091157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44435390789358591840243085 16663271546009471940091157)
                  ·
                    refine ⟨781090853719193997191773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16663271546009471940091157 781090853719193997191773)
                    ·
                      rfl

theorem cell23_4563507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 6].length) (baseStart_4563507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563507 prefixEnd_4563507 := by exact prefixLift 4563507
  have htrace : WordTrace (prefixWord ++ tailWord_4563507) baseStart_4563507 baseEnd_4563507 := by
    simpa [prefixWord, tailWord_4563507, baseEnd_4563507] using wordTrace_append hprefix tailTrace_4563507
  have hstable : (prefixWord ++ tailWord_4563507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563507).length < 2 ^ (prefixWord ++ tailWord_4563507).sum := by decide
  have hdescent : baseEnd_4563507 < baseStart_4563507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563514 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4]
def baseStart_4563514 : Nat := 118140960795 + 4563514 * 2 ^ 59
def prefixEnd_4563514 : Nat := 4983230072969 + 3 ^ 40 * 4563514 * 2
def baseEnd_4563514 : Nat := 2343276155522163464187787

theorem tailTrace_4563514 : CollatzResearch.WordTrace tailWord_4563514 prefixEnd_4563514 2343276155522163464187787 := by
  unfold tailWord_4563514
  simp only [CollatzResearch.WordTrace]
  refine ⟨41611257397293909746552399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110963353059450425990806397 41611257397293909746552399)
  ·
    refine ⟨62416886095940864619828599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41611257397293909746552399 62416886095940864619828599)
    ·
      refine ⟨93625329143911296929742899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62416886095940864619828599 93625329143911296929742899)
      ·
        refine ⟨140437993715866945394614349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93625329143911296929742899 140437993715866945394614349)
        ·
          refine ⟨52664247643450104522980381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140437993715866945394614349 52664247643450104522980381)
          ·
            refine ⟨19749092866293789196117643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52664247643450104522980381 19749092866293789196117643)
            ·
              refine ⟨29623639299440683794176465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19749092866293789196117643 29623639299440683794176465)
              ·
                refine ⟨22217729474580512845632349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29623639299440683794176465 22217729474580512845632349)
                ·
                  refine ⟨8331648552967692317112131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22217729474580512845632349 8331648552967692317112131)
                  ·
                    refine ⟨12497472829451538475668197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8331648552967692317112131 12497472829451538475668197)
                    ·
                      refine ⟨2343276155522163464187787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12497472829451538475668197 2343276155522163464187787)
                      ·
                        rfl

theorem cell23_4563514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_4563514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563514 prefixEnd_4563514 := by exact prefixLift 4563514
  have htrace : WordTrace (prefixWord ++ tailWord_4563514) baseStart_4563514 baseEnd_4563514 := by
    simpa [prefixWord, tailWord_4563514, baseEnd_4563514] using wordTrace_append hprefix tailTrace_4563514
  have hstable : (prefixWord ++ tailWord_4563514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563514).length < 2 ^ (prefixWord ++ tailWord_4563514).sum := by decide
  have hdescent : baseEnd_4563514 < baseStart_4563514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563531 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 5, 2, 2]
def baseStart_4563531 : Nat := 118140960795 + 4563531 * 2 ^ 59
def prefixEnd_4563531 : Nat := 4983230072969 + 3 ^ 40 * 4563531 * 2
def baseEnd_4563531 : Nat := 2343284884693289897675209

theorem tailTrace_4563531 : CollatzResearch.WordTrace tailWord_4563531 prefixEnd_4563531 2343284884693289897675209 := by
  unfold tailWord_4563531
  simp only [CollatzResearch.WordTrace]
  refine ⟨166445649630114050889578447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110963766420076033926385631 166445649630114050889578447)
  ·
    refine ⟨249668474445171076334367671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166445649630114050889578447 249668474445171076334367671)
    ·
      refine ⟨374502711667756614501551507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249668474445171076334367671 374502711667756614501551507)
      ·
        refine ⟨561754067501634921752327261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374502711667756614501551507 561754067501634921752327261)
        ·
          refine ⟨210657775313113095657122723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 561754067501634921752327261 210657775313113095657122723)
          ·
            refine ⟨315986662969669643485684085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210657775313113095657122723 315986662969669643485684085)
            ·
              refine ⟨29623749653406529076782883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 315986662969669643485684085 29623749653406529076782883)
              ·
                refine ⟨44435624480109793615174325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29623749653406529076782883 44435624480109793615174325)
                ·
                  refine ⟨4165839795010293151422593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44435624480109793615174325 4165839795010293151422593)
                  ·
                    refine ⟨3124379846257719863566945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4165839795010293151422593 3124379846257719863566945)
                    ·
                      refine ⟨2343284884693289897675209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3124379846257719863566945 2343284884693289897675209)
                      ·
                        rfl

theorem cell23_4563531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 2, 2].length) (baseStart_4563531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563531 prefixEnd_4563531 := by exact prefixLift 4563531
  have htrace : WordTrace (prefixWord ++ tailWord_4563531) baseStart_4563531 baseEnd_4563531 := by
    simpa [prefixWord, tailWord_4563531, baseEnd_4563531] using wordTrace_append hprefix tailTrace_4563531
  have hstable : (prefixWord ++ tailWord_4563531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563531).length < 2 ^ (prefixWord ++ tailWord_4563531).sum := by decide
  have hdescent : baseEnd_4563531 < baseStart_4563531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563544 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 1, 2, 4]
def baseStart_4563544 : Nat := 118140960795 + 4563544 * 2 ^ 59
def prefixEnd_4563544 : Nat := 4983230072969 + 3 ^ 40 * 4563544 * 2
def baseEnd_4563544 : Nat := 2343291559941798346812649

theorem tailTrace_4563544 : CollatzResearch.WordTrace tailWord_4563544 prefixEnd_4563544 2343291559941798346812649 := by
  unfold tailWord_4563544
  simp only [CollatzResearch.WordTrace]
  refine ⟨83223061889533477054900843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110964082519377969406534457 83223061889533477054900843)
  ·
    refine ⟨124834592834300215582351265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83223061889533477054900843 124834592834300215582351265)
    ·
      refine ⟨93625944625725161686763449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124834592834300215582351265 93625944625725161686763449)
      ·
        refine ⟨70219458469293871265072587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93625944625725161686763449 70219458469293871265072587)
        ·
          refine ⟨105329187703940806897608881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70219458469293871265072587 105329187703940806897608881)
          ·
            refine ⟨78996890777955605173206661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105329187703940806897608881 78996890777955605173206661)
            ·
              refine ⟨14811917020866675969976249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78996890777955605173206661 14811917020866675969976249)
              ·
                refine ⟨11108937765650006977482187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14811917020866675969976249 11108937765650006977482187)
                ·
                  refine ⟨16663406648475010466223281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11108937765650006977482187 16663406648475010466223281)
                  ·
                    refine ⟨12497554986356257849667461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16663406648475010466223281 12497554986356257849667461)
                    ·
                      refine ⟨2343291559941798346812649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12497554986356257849667461 2343291559941798346812649)
                      ·
                        rfl

theorem cell23_4563544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_4563544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563544 prefixEnd_4563544 := by exact prefixLift 4563544
  have htrace : WordTrace (prefixWord ++ tailWord_4563544) baseStart_4563544 baseEnd_4563544 := by
    simpa [prefixWord, tailWord_4563544, baseEnd_4563544] using wordTrace_append hprefix tailTrace_4563544
  have hstable : (prefixWord ++ tailWord_4563544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563544).length < 2 ^ (prefixWord ++ tailWord_4563544).sum := by decide
  have hdescent : baseEnd_4563544 < baseStart_4563544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563548 : List Nat := [2, 2, 4, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_4563548 : Nat := 118140960795 + 4563548 * 2 ^ 59
def prefixEnd_4563548 : Nat := 4983230072969 + 3 ^ 40 * 4563548 * 2
def baseEnd_4563548 : Nat := 2343293613864416331162631

theorem tailTrace_4563548 : CollatzResearch.WordTrace tailWord_4563548 prefixEnd_4563548 2343293613864416331162631 := by
  unfold tailWord_4563548
  simp only [CollatzResearch.WordTrace]
  refine ⟨83223134835526231396473649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110964179780701641861964865 83223134835526231396473649)
  ·
    refine ⟨62417351126644673547355237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83223134835526231396473649 62417351126644673547355237)
    ·
      refine ⟨11703253336245876290129107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62417351126644673547355237 11703253336245876290129107)
      ·
        refine ⟨17554880004368814435193661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11703253336245876290129107 17554880004368814435193661)
        ·
          refine ⟨6583080001638305413197623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17554880004368814435193661 6583080001638305413197623)
          ·
            refine ⟨9874620002457458119796435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6583080001638305413197623 9874620002457458119796435)
            ·
              refine ⟨14811930003686187179694653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9874620002457458119796435 14811930003686187179694653)
              ·
                refine ⟨5554473751382320192385495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14811930003686187179694653 5554473751382320192385495)
                ·
                  refine ⟨8331710627073480288578243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5554473751382320192385495 8331710627073480288578243)
                  ·
                    refine ⟨12497565940610220432867365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8331710627073480288578243 12497565940610220432867365)
                    ·
                      refine ⟨2343293613864416331162631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12497565940610220432867365 2343293613864416331162631)
                      ·
                        rfl

theorem cell23_4563548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_4563548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563548 prefixEnd_4563548 := by exact prefixLift 4563548
  have htrace : WordTrace (prefixWord ++ tailWord_4563548) baseStart_4563548 baseEnd_4563548 := by
    simpa [prefixWord, tailWord_4563548, baseEnd_4563548] using wordTrace_append hprefix tailTrace_4563548
  have hstable : (prefixWord ++ tailWord_4563548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563548).length < 2 ^ (prefixWord ++ tailWord_4563548).sum := by decide
  have hdescent : baseEnd_4563548 < baseStart_4563548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563564 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 3]
def baseStart_4563564 : Nat := 118140960795 + 4563564 * 2 ^ 59
def prefixEnd_4563564 : Nat := 4983230072969 + 3 ^ 40 * 4563564 * 2
def baseEnd_4563564 : Nat := 2343301829554888268562557

theorem tailTrace_4563564 : CollatzResearch.WordTrace tailWord_4563564 prefixEnd_4563564 2343301829554888268562557 := by
  unfold tailWord_4563564
  simp only [CollatzResearch.WordTrace]
  refine ⟨83223426619497248762764873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110964568825996331683686497 83223426619497248762764873)
  ·
    refine ⟨62417569964622936572073655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83223426619497248762764873 62417569964622936572073655)
    ·
      refine ⟨93626354946934404858110483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62417569964622936572073655 93626354946934404858110483)
      ·
        refine ⟨140439532420401607287165725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93626354946934404858110483 140439532420401607287165725)
        ·
          refine ⟨52664824657650602732687147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140439532420401607287165725 52664824657650602732687147)
          ·
            refine ⟨78997236986475904099030721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52664824657650602732687147 78997236986475904099030721)
            ·
              refine ⟨59247927739856928074273041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78997236986475904099030721 59247927739856928074273041)
              ·
                refine ⟨44435945804892696055704781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59247927739856928074273041 44435945804892696055704781)
                ·
                  refine ⟨16663479676834761020889293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44435945804892696055704781 16663479676834761020889293)
                  ·
                    refine ⟨6248804878813035382833485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16663479676834761020889293 6248804878813035382833485)
                    ·
                      refine ⟨2343301829554888268562557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6248804878813035382833485 2343301829554888268562557)
                      ·
                        rfl

theorem cell23_4563564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_4563564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563564 prefixEnd_4563564 := by exact prefixLift 4563564
  have htrace : WordTrace (prefixWord ++ tailWord_4563564) baseStart_4563564 baseEnd_4563564 := by
    simpa [prefixWord, tailWord_4563564, baseEnd_4563564] using wordTrace_append hprefix tailTrace_4563564
  have hstable : (prefixWord ++ tailWord_4563564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563564).length < 2 ^ (prefixWord ++ tailWord_4563564).sum := by decide
  have hdescent : baseEnd_4563564 < baseStart_4563564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563565 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 3, 2, 2]
def baseStart_4563565 : Nat := 118140960795 + 4563565 * 2 ^ 59
def prefixEnd_4563565 : Nat := 4983230072969 + 3 ^ 40 * 4563565 * 2
def baseEnd_4563565 : Nat := 2343302343035542764650053

theorem tailTrace_4563565 : CollatzResearch.WordTrace tailWord_4563565 prefixEnd_4563565 2343302343035542764650053 := by
  unfold tailWord_4563565
  simp only [CollatzResearch.WordTrace]
  refine ⟨166446889711990874696316149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110964593141327249797544099 166446889711990874696316149)
  ·
    refine ⟨15604395910499144502779639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166446889711990874696316149 15604395910499144502779639)
    ·
      refine ⟨23406593865748716754169459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15604395910499144502779639 23406593865748716754169459)
      ·
        refine ⟨35109890798623075131254189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23406593865748716754169459 35109890798623075131254189)
        ·
          refine ⟨13166209049483653174220321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35109890798623075131254189 13166209049483653174220321)
          ·
            refine ⟨9874656787112739880665241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13166209049483653174220321 9874656787112739880665241)
            ·
              refine ⟨7405992590334554910498931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9874656787112739880665241 7405992590334554910498931)
              ·
                refine ⟨11108988885501832365748397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7405992590334554910498931 11108988885501832365748397)
                ·
                  refine ⟨4165870832063187137155649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11108988885501832365748397 4165870832063187137155649)
                  ·
                    refine ⟨3124403124047390352866737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4165870832063187137155649 3124403124047390352866737)
                    ·
                      refine ⟨2343302343035542764650053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3124403124047390352866737 2343302343035542764650053)
                      ·
                        rfl

theorem cell23_4563565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_4563565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563565 prefixEnd_4563565 := by exact prefixLift 4563565
  have htrace : WordTrace (prefixWord ++ tailWord_4563565) baseStart_4563565 baseEnd_4563565 := by
    simpa [prefixWord, tailWord_4563565, baseEnd_4563565] using wordTrace_append hprefix tailTrace_4563565
  have hstable : (prefixWord ++ tailWord_4563565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563565).length < 2 ^ (prefixWord ++ tailWord_4563565).sum := by decide
  have hdescent : baseEnd_4563565 < baseStart_4563565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563567 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 1, 9]
def baseStart_4563567 : Nat := 118140960795 + 4563567 * 2 ^ 59
def prefixEnd_4563567 : Nat := 4983230072969 + 3 ^ 40 * 4563567 * 2
def baseEnd_4563567 : Nat := 781101123332283918941681

theorem tailTrace_4563567 : CollatzResearch.WordTrace tailWord_4563567 prefixEnd_4563567 781101123332283918941681 := by
  unfold tailWord_4563567
  simp only [CollatzResearch.WordTrace]
  refine ⟨166446962657983629037888955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110964641771989086025259303 166446962657983629037888955)
  ·
    refine ⟨249670443986975443556833433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166446962657983629037888955 249670443986975443556833433)
    ·
      refine ⟨187252832990231582667625075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249670443986975443556833433 187252832990231582667625075)
      ·
        refine ⟨280879249485347374001437613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187252832990231582667625075 280879249485347374001437613)
        ·
          refine ⟨105329718557005265250539105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 280879249485347374001437613 105329718557005265250539105)
          ·
            refine ⟨78997288917753948937904329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105329718557005265250539105 78997288917753948937904329)
            ·
              refine ⟨59247966688315461703428247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78997288917753948937904329 59247966688315461703428247)
              ·
                refine ⟨88871950032473192555142371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59247966688315461703428247 88871950032473192555142371)
                ·
                  refine ⟨133307925048709788832713557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88871950032473192555142371 133307925048709788832713557)
                  ·
                    refine ⟨781101123332283918941681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 133307925048709788832713557 781101123332283918941681)
                    ·
                      rfl

theorem cell23_4563567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 9].length) (baseStart_4563567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563567 prefixEnd_4563567 := by exact prefixLift 4563567
  have htrace : WordTrace (prefixWord ++ tailWord_4563567) baseStart_4563567 baseEnd_4563567 := by
    simpa [prefixWord, tailWord_4563567, baseEnd_4563567] using wordTrace_append hprefix tailTrace_4563567
  have hstable : (prefixWord ++ tailWord_4563567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563567).length < 2 ^ (prefixWord ++ tailWord_4563567).sum := by decide
  have hdescent : baseEnd_4563567 < baseStart_4563567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563608 : List Nat := [2, 1, 2, 4, 1, 1, 1, 5, 1, 3, 2]
def baseStart_4563608 : Nat := 118140960795 + 4563608 * 2 ^ 59
def prefixEnd_4563608 : Nat := 4983230072969 + 3 ^ 40 * 4563608 * 2
def baseEnd_4563608 : Nat := 2343324422703686096412355

theorem tailTrace_4563608 : CollatzResearch.WordTrace tailWord_4563608 prefixEnd_4563608 2343324422703686096412355 := by
  unfold tailWord_4563608
  simp only [CollatzResearch.WordTrace]
  refine ⟨83224229025417546520065739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110965638700556728693420985 83224229025417546520065739)
  ·
    refine ⟨124836343538126319780098609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83224229025417546520065739 124836343538126319780098609)
    ·
      refine ⟨93627257653594739835073957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124836343538126319780098609 93627257653594739835073957)
      ·
        refine ⟨17555110810049013719076367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93627257653594739835073957 17555110810049013719076367)
        ·
          refine ⟨26332666215073520578614551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17555110810049013719076367 26332666215073520578614551)
          ·
            refine ⟨39498999322610280867921827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26332666215073520578614551 39498999322610280867921827)
            ·
              refine ⟨59248498983915421301882741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39498999322610280867921827 59248498983915421301882741)
              ·
                refine ⟨5554546779742070747051507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59248498983915421301882741 5554546779742070747051507)
                ·
                  refine ⟨8331820169613106120577261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5554546779742070747051507 8331820169613106120577261)
                  ·
                    refine ⟨3124432563604914795216473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8331820169613106120577261 3124432563604914795216473)
                    ·
                      refine ⟨2343324422703686096412355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3124432563604914795216473 2343324422703686096412355)
                      ·
                        rfl

theorem cell23_4563608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_4563608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563608 prefixEnd_4563608 := by exact prefixLift 4563608
  have htrace : WordTrace (prefixWord ++ tailWord_4563608) baseStart_4563608 baseEnd_4563608 := by
    simpa [prefixWord, tailWord_4563608, baseEnd_4563608] using wordTrace_append hprefix tailTrace_4563608
  have hstable : (prefixWord ++ tailWord_4563608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563608).length < 2 ^ (prefixWord ++ tailWord_4563608).sum := by decide
  have hdescent : baseEnd_4563608 < baseStart_4563608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563634 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_4563634 : Nat := 118140960795 + 4563634 * 2 ^ 59
def prefixEnd_4563634 : Nat := 4983230072969 + 3 ^ 40 * 4563634 * 2
def baseEnd_4563634 : Nat := 2343337773200702994687235

theorem tailTrace_4563634 : CollatzResearch.WordTrace tailWord_4563634 prefixEnd_4563634 2343337773200702994687235 := by
  unfold tailWord_4563634
  simp only [CollatzResearch.WordTrace]
  refine ⟨41612351587185224870144489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110966270899160599653718637 41612351587185224870144489)
  ·
    refine ⟨31209263690388918652608367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41612351587185224870144489 31209263690388918652608367)
    ·
      refine ⟨46813895535583377978912551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31209263690388918652608367 46813895535583377978912551)
      ·
        refine ⟨70220843303375066968368827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46813895535583377978912551 70220843303375066968368827)
        ·
          refine ⟨105331264955062600452553241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70220843303375066968368827 105331264955062600452553241)
          ·
            refine ⟨78998448716296950339414931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105331264955062600452553241 78998448716296950339414931)
            ·
              refine ⟨118497673074445425509122397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78998448716296950339414931 118497673074445425509122397)
              ·
                refine ⟨44436627402917034565920899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118497673074445425509122397 44436627402917034565920899)
                ·
                  refine ⟨66654941104375551848881349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44436627402917034565920899 66654941104375551848881349)
                  ·
                    refine ⟨12497801457070415971665253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66654941104375551848881349 12497801457070415971665253)
                    ·
                      refine ⟨2343337773200702994687235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12497801457070415971665253 2343337773200702994687235)
                      ·
                        rfl

theorem cell23_4563634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_4563634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563634 prefixEnd_4563634 := by exact prefixLift 4563634
  have htrace : WordTrace (prefixWord ++ tailWord_4563634) baseStart_4563634 baseEnd_4563634 := by
    simpa [prefixWord, tailWord_4563634, baseEnd_4563634] using wordTrace_append hprefix tailTrace_4563634
  have hstable : (prefixWord ++ tailWord_4563634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563634).length < 2 ^ (prefixWord ++ tailWord_4563634).sum := by decide
  have hdescent : baseEnd_4563634 < baseStart_4563634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563644 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 9]
def baseStart_4563644 : Nat := 118140960795 + 4563644 * 2 ^ 59
def prefixEnd_4563644 : Nat := 4983230072969 + 3 ^ 40 * 4563644 * 2
def baseEnd_4563644 : Nat := 260371434223027550618021

theorem tailTrace_4563644 : CollatzResearch.WordTrace tailWord_4563644 prefixEnd_4563644 260371434223027550618021 := by
  unfold tailWord_4563644
  simp only [CollatzResearch.WordTrace]
  refine ⟨83224885539352335594220993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110966514052469780792294657 83224885539352335594220993)
  ·
    refine ⟨62418664154514251695665745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83224885539352335594220993 62418664154514251695665745)
    ·
      refine ⟨46813998115885688771749309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62418664154514251695665745 46813998115885688771749309)
      ·
        refine ⟨17555249293457133289405991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46813998115885688771749309 17555249293457133289405991)
        ·
          refine ⟨26332873940185699934108987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17555249293457133289405991 26332873940185699934108987)
          ·
            refine ⟨39499310910278549901163481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26332873940185699934108987 39499310910278549901163481)
            ·
              refine ⟨29624483182708912425872611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39499310910278549901163481 29624483182708912425872611)
              ·
                refine ⟨44436724774063368638808917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29624483182708912425872611 44436724774063368638808917)
                ·
                  refine ⟨260371434223027550618021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44436724774063368638808917 260371434223027550618021)
                  ·
                    rfl

theorem cell23_4563644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 9].length) (baseStart_4563644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563644 prefixEnd_4563644 := by exact prefixLift 4563644
  have htrace : WordTrace (prefixWord ++ tailWord_4563644) baseStart_4563644 baseEnd_4563644 := by
    simpa [prefixWord, tailWord_4563644, baseEnd_4563644] using wordTrace_append hprefix tailTrace_4563644
  have hstable : (prefixWord ++ tailWord_4563644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563644).length < 2 ^ (prefixWord ++ tailWord_4563644).sum := by decide
  have hdescent : baseEnd_4563644 < baseStart_4563644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563688 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_4563688 : Nat := 118140960795 + 4563688 * 2 ^ 59
def prefixEnd_4563688 : Nat := 4983230072969 + 3 ^ 40 * 4563688 * 2
def baseEnd_4563688 : Nat := 2343365501156045783411987

theorem tailTrace_4563688 : CollatzResearch.WordTrace tailWord_4563688 prefixEnd_4563688 2343365501156045783411987 := by
  unfold tailWord_4563688
  simp only [CollatzResearch.WordTrace]
  refine ⟨83225687945272633351521859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110967583927030177802029145 83225687945272633351521859)
  ·
    refine ⟨124838531917908950027282789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83225687945272633351521859 124838531917908950027282789)
    ·
      refine ⟨23407224734607928130115523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124838531917908950027282789 23407224734607928130115523)
      ·
        refine ⟨35110837101911892195173285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23407224734607928130115523 35110837101911892195173285)
        ·
          refine ⟨6583281956608479786594991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35110837101911892195173285 6583281956608479786594991)
          ·
            refine ⟨9874922934912719679892487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6583281956608479786594991 9874922934912719679892487)
            ·
              refine ⟨14812384402369079519838731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9874922934912719679892487 14812384402369079519838731)
              ·
                refine ⟨22218576603553619279758097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14812384402369079519838731 22218576603553619279758097)
                ·
                  refine ⟨16663932452665214459818573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22218576603553619279758097 16663932452665214459818573)
                  ·
                    refine ⟨6248974669749455422431965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16663932452665214459818573 6248974669749455422431965)
                    ·
                      refine ⟨2343365501156045783411987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6248974669749455422431965 2343365501156045783411987)
                      ·
                        rfl

theorem cell23_4563688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_4563688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563688 prefixEnd_4563688 := by exact prefixLift 4563688
  have htrace : WordTrace (prefixWord ++ tailWord_4563688) baseStart_4563688 baseEnd_4563688 := by
    simpa [prefixWord, tailWord_4563688, baseEnd_4563688] using wordTrace_append hprefix tailTrace_4563688
  have hstable : (prefixWord ++ tailWord_4563688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563688).length < 2 ^ (prefixWord ++ tailWord_4563688).sum := by decide
  have hdescent : baseEnd_4563688 < baseStart_4563688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563708 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 2, 5]
def baseStart_4563708 : Nat := 118140960795 + 4563708 * 2 ^ 59
def prefixEnd_4563708 : Nat := 4983230072969 + 3 ^ 40 * 4563708 * 2
def baseEnd_4563708 : Nat := 781125256923045235053965

theorem tailTrace_4563708 : CollatzResearch.WordTrace tailWord_4563708 prefixEnd_4563708 781125256923045235053965 := by
  unfold tailWord_4563708
  simp only [CollatzResearch.WordTrace]
  refine ⟨83226052675236405059385889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110968070233648540079181185 83226052675236405059385889)
  ·
    refine ⟨62419539506427303794539417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83226052675236405059385889 62419539506427303794539417)
    ·
      refine ⟨46814654629820477845904563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62419539506427303794539417 46814654629820477845904563)
      ·
        refine ⟨70221981944730716768856845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46814654629820477845904563 70221981944730716768856845)
        ·
          refine ⟨26333243229274018788321317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70221981944730716768856845 26333243229274018788321317)
          ·
            refine ⟨4937483105488878522810247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26333243229274018788321317 4937483105488878522810247)
            ·
              refine ⟨7406224658233317784215371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4937483105488878522810247 7406224658233317784215371)
              ·
                refine ⟨11109336987349976676323057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7406224658233317784215371 11109336987349976676323057)
                ·
                  refine ⟨8332002740512482507242293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11109336987349976676323057 8332002740512482507242293)
                  ·
                    refine ⟨781125256923045235053965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8332002740512482507242293 781125256923045235053965)
                    ·
                      rfl

theorem cell23_4563708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_4563708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563708 prefixEnd_4563708 := by exact prefixLift 4563708
  have htrace : WordTrace (prefixWord ++ tailWord_4563708) baseStart_4563708 baseEnd_4563708 := by
    simpa [prefixWord, tailWord_4563708, baseEnd_4563708] using wordTrace_append hprefix tailTrace_4563708
  have hstable : (prefixWord ++ tailWord_4563708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563708).length < 2 ^ (prefixWord ++ tailWord_4563708).sum := by decide
  have hdescent : baseEnd_4563708 < baseStart_4563708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563711 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 3, 6, 2]
def baseStart_4563711 : Nat := 118140960795 + 4563711 * 2 ^ 59
def prefixEnd_4563711 : Nat := 4983230072969 + 3 ^ 40 * 4563711 * 2
def baseEnd_4563711 : Nat := 2343377311211099193424381

theorem tailTrace_4563711 : CollatzResearch.WordTrace tailWord_4563711 prefixEnd_4563711 2343377311211099193424381 := by
  unfold tailWord_4563711
  simp only [CollatzResearch.WordTrace]
  refine ⟨166452214769461941631130987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110968143179641294420753991 166452214769461941631130987)
  ·
    refine ⟨249678322154192912446696481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166452214769461941631130987 249678322154192912446696481)
    ·
      refine ⟨187258741615644684335022361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249678322154192912446696481 187258741615644684335022361)
      ·
        refine ⟨140444056211733513251266771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187258741615644684335022361 140444056211733513251266771)
        ·
          refine ⟨210666084317600269876900157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140444056211733513251266771 210666084317600269876900157)
          ·
            refine ⟨78999781619100101203837559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210666084317600269876900157 78999781619100101203837559)
            ·
              refine ⟨118499672428650151805756339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78999781619100101203837559 118499672428650151805756339)
              ·
                refine ⟨177749508642975227708634509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118499672428650151805756339 177749508642975227708634509)
                ·
                  refine ⟨66656065741115710390737941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177749508642975227708634509 66656065741115710390737941)
                  ·
                    refine ⟨3124503081614798924565841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66656065741115710390737941 3124503081614798924565841)
                    ·
                      refine ⟨2343377311211099193424381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3124503081614798924565841 2343377311211099193424381)
                      ·
                        rfl

theorem cell23_4563711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 6, 2].length) (baseStart_4563711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563711 prefixEnd_4563711 := by exact prefixLift 4563711
  have htrace : WordTrace (prefixWord ++ tailWord_4563711) baseStart_4563711 baseEnd_4563711 := by
    simpa [prefixWord, tailWord_4563711, baseEnd_4563711] using wordTrace_append hprefix tailTrace_4563711
  have hstable : (prefixWord ++ tailWord_4563711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563711).length < 2 ^ (prefixWord ++ tailWord_4563711).sum := by decide
  have hdescent : baseEnd_4563711 < baseStart_4563711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563731 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 3]
def baseStart_4563731 : Nat := 118140960795 + 4563731 * 2 ^ 59
def prefixEnd_4563731 : Nat := 4983230072969 + 3 ^ 40 * 4563731 * 2
def baseEnd_4563731 : Nat := 2343387580824189115174289

theorem tailTrace_4563731 : CollatzResearch.WordTrace tailWord_4563731 prefixEnd_4563731 2343387580824189115174289 := by
  unfold tailWord_4563731
  simp only [CollatzResearch.WordTrace]
  refine ⟨166452944229389485046859047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110968629486259656697906031 166452944229389485046859047)
  ·
    refine ⟨249679416344084227570288571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166452944229389485046859047 249679416344084227570288571)
    ·
      refine ⟨374519124516126341355432857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249679416344084227570288571 374519124516126341355432857)
      ·
        refine ⟨280889343387094756016574643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374519124516126341355432857 280889343387094756016574643)
        ·
          refine ⟨421334015080642134024861965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280889343387094756016574643 421334015080642134024861965)
          ·
            refine ⟨158000255655240800259323237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 421334015080642134024861965 158000255655240800259323237)
            ·
              refine ⟨29625047935357650048623107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158000255655240800259323237 29625047935357650048623107)
              ·
                refine ⟨44437571903036475072934661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29625047935357650048623107 44437571903036475072934661)
                ·
                  refine ⟨8332044731819339076175249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44437571903036475072934661 8332044731819339076175249)
                  ·
                    refine ⟨6249033548864504307131437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8332044731819339076175249 6249033548864504307131437)
                    ·
                      refine ⟨2343387580824189115174289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6249033548864504307131437 2343387580824189115174289)
                      ·
                        rfl

theorem cell23_4563731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 3].length) (baseStart_4563731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563731 prefixEnd_4563731 := by exact prefixLift 4563731
  have htrace : WordTrace (prefixWord ++ tailWord_4563731) baseStart_4563731 baseEnd_4563731 := by
    simpa [prefixWord, tailWord_4563731, baseEnd_4563731] using wordTrace_append hprefix tailTrace_4563731
  have hstable : (prefixWord ++ tailWord_4563731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563731).length < 2 ^ (prefixWord ++ tailWord_4563731).sum := by decide
  have hdescent : baseEnd_4563731 < baseStart_4563731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563738 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 3, 4]
def baseStart_4563738 : Nat := 118140960795 + 4563738 * 2 ^ 59
def prefixEnd_4563738 : Nat := 4983230072969 + 3 ^ 40 * 4563738 * 2
def baseEnd_4563738 : Nat := 781130391729590195928919

theorem tailTrace_4563738 : CollatzResearch.WordTrace tailWord_4563738 prefixEnd_4563738 781130391729590195928919 := by
  unfold tailWord_4563738
  simp only [CollatzResearch.WordTrace]
  refine ⟨41613299885091031310590967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110968799693576083494909245 41613299885091031310590967)
  ·
    refine ⟨62419949827636546965886451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41613299885091031310590967 62419949827636546965886451)
    ·
      refine ⟨93629924741454820448829677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62419949827636546965886451 93629924741454820448829677)
      ·
        refine ⟨35111221778045557668311129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93629924741454820448829677 35111221778045557668311129)
        ·
          refine ⟨26333416333534168251233347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35111221778045557668311129 26333416333534168251233347)
          ·
            refine ⟨39500124500301252376850021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26333416333534168251233347 39500124500301252376850021)
            ·
              refine ⟨7406273343806484820659379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39500124500301252376850021 7406273343806484820659379)
              ·
                refine ⟨11109410015709727230989069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7406273343806484820659379 11109410015709727230989069)
                ·
                  refine ⟨4166028755891147711620901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11109410015709727230989069 4166028755891147711620901)
                  ·
                    refine ⟨781130391729590195928919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4166028755891147711620901 781130391729590195928919)
                    ·
                      rfl

theorem cell23_4563738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_4563738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563738 prefixEnd_4563738 := by exact prefixLift 4563738
  have htrace : WordTrace (prefixWord ++ tailWord_4563738) baseStart_4563738 baseEnd_4563738 := by
    simpa [prefixWord, tailWord_4563738, baseEnd_4563738] using wordTrace_append hprefix tailTrace_4563738
  have hstable : (prefixWord ++ tailWord_4563738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563738).length < 2 ^ (prefixWord ++ tailWord_4563738).sum := by decide
  have hdescent : baseEnd_4563738 < baseStart_4563738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563761 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 2, 5, 3]
def baseStart_4563761 : Nat := 118140960795 + 4563761 * 2 ^ 59
def prefixEnd_4563761 : Nat := 4983230072969 + 3 ^ 40 * 4563761 * 2
def baseEnd_4563761 : Nat := 2343402985243823997799151

theorem tailTrace_4563761 : CollatzResearch.WordTrace tailWord_4563761 prefixEnd_4563761 2343402985243823997799151 := by
  unfold tailWord_4563761
  simp only [CollatzResearch.WordTrace]
  refine ⟨166454038419280800170451137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110969358946187200113634091 166454038419280800170451137)
  ·
    refine ⟨124840528814460600127838353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166454038419280800170451137 124840528814460600127838353)
    ·
      refine ⟨93630396610845450095878765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124840528814460600127838353 93630396610845450095878765)
      ·
        refine ⟨35111398729067043785954537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93630396610845450095878765 35111398729067043785954537)
        ·
          refine ⟨26333549046800282839465903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35111398729067043785954537 26333549046800282839465903)
          ·
            refine ⟨39500323570200424259198855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26333549046800282839465903 39500323570200424259198855)
            ·
              refine ⟨59250485355300636388798283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39500323570200424259198855 59250485355300636388798283)
              ·
                refine ⟨88875728032950954583197425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59250485355300636388798283 88875728032950954583197425)
                ·
                  refine ⟨66656796024713215937398069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88875728032950954583197425 66656796024713215937398069)
                  ·
                    refine ⟨6249074627316863994131069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66656796024713215937398069 6249074627316863994131069)
                    ·
                      refine ⟨2343402985243823997799151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6249074627316863994131069 2343402985243823997799151)
                      ·
                        rfl

theorem cell23_4563761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_4563761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563761 prefixEnd_4563761 := by exact prefixLift 4563761
  have htrace : WordTrace (prefixWord ++ tailWord_4563761) baseStart_4563761 baseEnd_4563761 := by
    simpa [prefixWord, tailWord_4563761, baseEnd_4563761] using wordTrace_append hprefix tailTrace_4563761
  have hstable : (prefixWord ++ tailWord_4563761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563761).length < 2 ^ (prefixWord ++ tailWord_4563761).sum := by decide
  have hdescent : baseEnd_4563761 < baseStart_4563761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563789 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_4563789 : Nat := 118140960795 + 4563789 * 2 ^ 59
def prefixEnd_4563789 : Nat := 4983230072969 + 3 ^ 40 * 4563789 * 2
def baseEnd_4563789 : Nat := 781139120900716629416341

theorem tailTrace_4563789 : CollatzResearch.WordTrace tailWord_4563789 prefixEnd_4563789 781139120900716629416341 := by
  unfold tailWord_4563789
  simp only [CollatzResearch.WordTrace]
  refine ⟨166455059663179360952470421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110970039775452907301646947 166455059663179360952470421)
  ·
    refine ⟨7802580921711532544647051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 166455059663179360952470421 7802580921711532544647051)
    ·
      refine ⟨11703871382567298816970577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7802580921711532544647051 11703871382567298816970577)
      ·
        refine ⟨8777903536925474112727933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11703871382567298816970577 8777903536925474112727933)
        ·
          refine ⟨3291713826347052792272975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8777903536925474112727933 3291713826347052792272975)
          ·
            refine ⟨4937570739520579188409463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3291713826347052792272975 4937570739520579188409463)
            ·
              refine ⟨7406356109280868782614195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4937570739520579188409463 7406356109280868782614195)
              ·
                refine ⟨11109534163921303173921293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7406356109280868782614195 11109534163921303173921293)
                ·
                  refine ⟨4166075311470488690220485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11109534163921303173921293 4166075311470488690220485)
                  ·
                    refine ⟨781139120900716629416341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4166075311470488690220485 781139120900716629416341)
                    ·
                      rfl

theorem cell23_4563789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_4563789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563789 prefixEnd_4563789 := by exact prefixLift 4563789
  have htrace : WordTrace (prefixWord ++ tailWord_4563789) baseStart_4563789 baseEnd_4563789 := by
    simpa [prefixWord, tailWord_4563789, baseEnd_4563789] using wordTrace_append hprefix tailTrace_4563789
  have hstable : (prefixWord ++ tailWord_4563789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563789).length < 2 ^ (prefixWord ++ tailWord_4563789).sum := by decide
  have hdescent : baseEnd_4563789 < baseStart_4563789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563795 : List Nat := [1, 1, 1, 2, 1, 1, 3, 8, 1, 1, 3]
def baseStart_4563795 : Nat := 118140960795 + 4563795 * 2 ^ 59
def prefixEnd_4563795 : Nat := 4983230072969 + 3 ^ 40 * 4563795 * 2
def baseEnd_4563795 : Nat := 2343420443586076864773995

theorem tailTrace_4563795 : CollatzResearch.WordTrace tailWord_4563795 prefixEnd_4563795 2343420443586076864773995 := by
  unfold tailWord_4563795
  simp only [CollatzResearch.WordTrace]
  refine ⟨166455278501157623977188839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110970185667438415984792559 166455278501157623977188839)
  ·
    refine ⟨249682917751736435965783259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166455278501157623977188839 249682917751736435965783259)
    ·
      refine ⟨374524376627604653948674889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249682917751736435965783259 374524376627604653948674889)
      ·
        refine ⟨280893282470703490461506167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374524376627604653948674889 280893282470703490461506167)
        ·
          refine ⟨421339923706055235692259251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280893282470703490461506167 421339923706055235692259251)
          ·
            refine ⟨632009885559082853538388877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421339923706055235692259251 632009885559082853538388877)
            ·
              refine ⟨237003707084656070076895829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 632009885559082853538388877 237003707084656070076895829)
              ·
                refine ⟨2777387192398313321213623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 237003707084656070076895829 2777387192398313321213623)
                ·
                  refine ⟨4166080788597469981820435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2777387192398313321213623 4166080788597469981820435)
                  ·
                    refine ⟨6249121182896204972730653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4166080788597469981820435 6249121182896204972730653)
                    ·
                      refine ⟨2343420443586076864773995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6249121182896204972730653 2343420443586076864773995)
                      ·
                        rfl

theorem cell23_4563795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 1, 1, 3].length) (baseStart_4563795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563795 prefixEnd_4563795 := by exact prefixLift 4563795
  have htrace : WordTrace (prefixWord ++ tailWord_4563795) baseStart_4563795 baseEnd_4563795 := by
    simpa [prefixWord, tailWord_4563795, baseEnd_4563795] using wordTrace_append hprefix tailTrace_4563795
  have hstable : (prefixWord ++ tailWord_4563795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563795).length < 2 ^ (prefixWord ++ tailWord_4563795).sum := by decide
  have hdescent : baseEnd_4563795 < baseStart_4563795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563815 : List Nat := [1, 1, 5, 1, 2, 4, 1, 2, 1, 5]
def baseStart_4563815 : Nat := 118140960795 + 4563815 * 2 ^ 59
def prefixEnd_4563815 : Nat := 4983230072969 + 3 ^ 40 * 4563815 * 2
def baseEnd_4563815 : Nat := 781143571066388928841301

theorem tailTrace_4563815 : CollatzResearch.WordTrace tailWord_4563815 prefixEnd_4563815 781143571066388928841301 := by
  unfold tailWord_4563815
  simp only [CollatzResearch.WordTrace]
  refine ⟨166456007961085167392916899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110970671974056778261944599 166456007961085167392916899)
  ·
    refine ⟨249684011941627751089375349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166456007961085167392916899 249684011941627751089375349)
    ·
      refine ⟨23407876119527601664628939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 249684011941627751089375349 23407876119527601664628939)
      ·
        refine ⟨35111814179291402496943409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23407876119527601664628939 35111814179291402496943409)
        ·
          refine ⟨26333860634468551872707557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35111814179291402496943409 26333860634468551872707557)
          ·
            refine ⟨4937598868962853476132667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26333860634468551872707557 4937598868962853476132667)
            ·
              refine ⟨7406398303444280214199001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4937598868962853476132667 7406398303444280214199001)
              ·
                refine ⟨5554798727583210160649251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7406398303444280214199001 5554798727583210160649251)
                ·
                  refine ⟨8332198091374815240973877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5554798727583210160649251 8332198091374815240973877)
                  ·
                    refine ⟨781143571066388928841301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8332198091374815240973877 781143571066388928841301)
                    ·
                      rfl

theorem cell23_4563815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_4563815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563815 prefixEnd_4563815 := by exact prefixLift 4563815
  have htrace : WordTrace (prefixWord ++ tailWord_4563815) baseStart_4563815 baseEnd_4563815 := by
    simpa [prefixWord, tailWord_4563815, baseEnd_4563815] using wordTrace_append hprefix tailTrace_4563815
  have hstable : (prefixWord ++ tailWord_4563815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563815).length < 2 ^ (prefixWord ++ tailWord_4563815).sum := by decide
  have hdescent : baseEnd_4563815 < baseStart_4563815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563845 : List Nat := [1, 3, 1, 1, 3, 4, 2, 2, 2, 4]
def baseStart_4563845 : Nat := 118140960795 + 4563845 * 2 ^ 59
def prefixEnd_4563845 : Nat := 4983230072969 + 3 ^ 40 * 4563845 * 2
def baseEnd_4563845 : Nat := 781148705872933889716255

theorem tailTrace_4563845 : CollatzResearch.WordTrace tailWord_4563845 prefixEnd_4563845 781148705872933889716255 := by
  unfold tailWord_4563845
  simp only [CollatzResearch.WordTrace]
  refine ⟨166457102150976482516508989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110971401433984321677672659 166457102150976482516508989)
  ·
    refine ⟨62421413306616180943690871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166457102150976482516508989 62421413306616180943690871)
    ·
      refine ⟨93632119959924271415536307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62421413306616180943690871 93632119959924271415536307)
      ·
        refine ⟨140448179939886407123304461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93632119959924271415536307 140448179939886407123304461)
        ·
          refine ⟨52668067477457402671239173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140448179939886407123304461 52668067477457402671239173)
          ·
            refine ⟨9875262652023263000857345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52668067477457402671239173 9875262652023263000857345)
            ·
              refine ⟨7406446989017447250643009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9875262652023263000857345 7406446989017447250643009)
              ·
                refine ⟨5554835241763085437982257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7406446989017447250643009 5554835241763085437982257)
                ·
                  refine ⟨4166126431322314078486693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5554835241763085437982257 4166126431322314078486693)
                  ·
                    refine ⟨781148705872933889716255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4166126431322314078486693 781148705872933889716255)
                    ·
                      rfl

theorem cell23_4563845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_4563845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563845 prefixEnd_4563845 := by exact prefixLift 4563845
  have htrace : WordTrace (prefixWord ++ tailWord_4563845) baseStart_4563845 baseEnd_4563845 := by
    simpa [prefixWord, tailWord_4563845, baseEnd_4563845] using wordTrace_append hprefix tailTrace_4563845
  have hstable : (prefixWord ++ tailWord_4563845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563845).length < 2 ^ (prefixWord ++ tailWord_4563845).sum := by decide
  have hdescent : baseEnd_4563845 < baseStart_4563845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563862 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_4563862 : Nat := 118140960795 + 4563862 * 2 ^ 59
def prefixEnd_4563862 : Nat := 4983230072969 + 3 ^ 40 * 4563862 * 2
def baseEnd_4563862 : Nat := 781151615596642700878729

theorem tailTrace_4563862 : CollatzResearch.WordTrace tailWord_4563862 prefixEnd_4563862 781151615596642700878729 := by
  unfold tailWord_4563862
  simp only [CollatzResearch.WordTrace]
  refine ⟨10403607636994680901242365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110971814794609929613251893 10403607636994680901242365)
  ·
    refine ⟨3901352863873005337965887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10403607636994680901242365 3901352863873005337965887)
    ·
      refine ⟨5852029295809508006948831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3901352863873005337965887 5852029295809508006948831)
      ·
        refine ⟨8778043943714262010423247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5852029295809508006948831 8778043943714262010423247)
        ·
          refine ⟨13167065915571393015634871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8778043943714262010423247 13167065915571393015634871)
          ·
            refine ⟨19750598873357089523452307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13167065915571393015634871 19750598873357089523452307)
            ·
              refine ⟨29625898310035634285178461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19750598873357089523452307 29625898310035634285178461)
              ·
                refine ⟨11109711866263362856941923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29625898310035634285178461 11109711866263362856941923)
                ·
                  refine ⟨16664567799395044285412885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11109711866263362856941923 16664567799395044285412885)
                  ·
                    refine ⟨781151615596642700878729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16664567799395044285412885 781151615596642700878729)
                    ·
                      rfl

theorem cell23_4563862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_4563862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563862 prefixEnd_4563862 := by exact prefixLift 4563862
  have htrace : WordTrace (prefixWord ++ tailWord_4563862) baseStart_4563862 baseEnd_4563862 := by
    simpa [prefixWord, tailWord_4563862, baseEnd_4563862] using wordTrace_append hprefix tailTrace_4563862
  have hstable : (prefixWord ++ tailWord_4563862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563862).length < 2 ^ (prefixWord ++ tailWord_4563862).sum := by decide
  have hdescent : baseEnd_4563862 < baseStart_4563862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563881 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 2, 2, 5]
def baseStart_4563881 : Nat := 118140960795 + 4563881 * 2 ^ 59
def prefixEnd_4563881 : Nat := 4983230072969 + 3 ^ 40 * 4563881 * 2
def baseEnd_4563881 : Nat := 2343464602922363528298599

theorem tailTrace_4563881 : CollatzResearch.WordTrace tailWord_4563881 prefixEnd_4563881 2343464602922363528298599 := by
  unfold tailWord_4563881
  simp only [CollatzResearch.WordTrace]
  refine ⟨166458415178846060664819497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110972276785897373776546331 166458415178846060664819497)
  ·
    refine ⟨124843811384134545498614623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166458415178846060664819497 124843811384134545498614623)
    ·
      refine ⟨187265717076201818247921935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124843811384134545498614623 187265717076201818247921935)
      ·
        refine ⟨280898575614302727371882903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187265717076201818247921935 280898575614302727371882903)
        ·
          refine ⟨421347863421454091057824355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280898575614302727371882903 421347863421454091057824355)
          ·
            refine ⟨632021795132181136586736533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421347863421454091057824355 632021795132181136586736533)
            ·
              refine ⟨29626021646820990777503275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 632021795132181136586736533 29626021646820990777503275)
              ·
                refine ⟨44439032470231486166254913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29626021646820990777503275 44439032470231486166254913)
                ·
                  refine ⟨33329274352673614624691185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44439032470231486166254913 33329274352673614624691185)
                  ·
                    refine ⟨24996955764505210968518389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33329274352673614624691185 24996955764505210968518389)
                    ·
                      refine ⟨2343464602922363528298599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24996955764505210968518389 2343464602922363528298599)
                      ·
                        rfl

theorem cell23_4563881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_4563881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563881 prefixEnd_4563881 := by exact prefixLift 4563881
  have htrace : WordTrace (prefixWord ++ tailWord_4563881) baseStart_4563881 baseEnd_4563881 := by
    simpa [prefixWord, tailWord_4563881, baseEnd_4563881] using wordTrace_append hprefix tailTrace_4563881
  have hstable : (prefixWord ++ tailWord_4563881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563881).length < 2 ^ (prefixWord ++ tailWord_4563881).sum := by decide
  have hdescent : baseEnd_4563881 < baseStart_4563881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563889 : List Nat := [1, 2, 2, 4, 3, 2, 2, 1, 1, 2, 3]
def baseStart_4563889 : Nat := 118140960795 + 4563889 * 2 ^ 59
def prefixEnd_4563889 : Nat := 4983230072969 + 3 ^ 40 * 4563889 * 2
def baseEnd_4563889 : Nat := 2343468710767599496998563

theorem tailTrace_4563889 : CollatzResearch.WordTrace tailWord_4563889 prefixEnd_4563889 2343468710767599496998563 := by
  unfold tailWord_4563889
  simp only [CollatzResearch.WordTrace]
  refine ⟨166458706962817078031110721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110972471308544718687407147 166458706962817078031110721)
  ·
    refine ⟨124844030222112808523333041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166458706962817078031110721 124844030222112808523333041)
    ·
      refine ⟨93633022666584606392499781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124844030222112808523333041 93633022666584606392499781)
      ·
        refine ⟨17556191749984613698593709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93633022666584606392499781 17556191749984613698593709)
        ·
          refine ⟨6583571906244230136972641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17556191749984613698593709 6583571906244230136972641)
          ·
            refine ⟨4937678929683172602729481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6583571906244230136972641 4937678929683172602729481)
            ·
              refine ⟨3703259197262379452047111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4937678929683172602729481 3703259197262379452047111)
              ·
                refine ⟨5554888795893569178070667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3703259197262379452047111 5554888795893569178070667)
                ·
                  refine ⟨8332333193840353767106001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5554888795893569178070667 8332333193840353767106001)
                  ·
                    refine ⟨6249249895380265325329501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8332333193840353767106001 6249249895380265325329501)
                    ·
                      refine ⟨2343468710767599496998563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6249249895380265325329501 2343468710767599496998563)
                      ·
                        rfl

theorem cell23_4563889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_4563889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563889 prefixEnd_4563889 := by exact prefixLift 4563889
  have htrace : WordTrace (prefixWord ++ tailWord_4563889) baseStart_4563889 baseEnd_4563889 := by
    simpa [prefixWord, tailWord_4563889, baseEnd_4563889] using wordTrace_append hprefix tailTrace_4563889
  have hstable : (prefixWord ++ tailWord_4563889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563889).length < 2 ^ (prefixWord ++ tailWord_4563889).sum := by decide
  have hdescent : baseEnd_4563889 < baseStart_4563889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563891 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 4]
def baseStart_4563891 : Nat := 118140960795 + 4563891 * 2 ^ 59
def prefixEnd_4563891 : Nat := 4983230072969 + 3 ^ 40 * 4563891 * 2
def baseEnd_4563891 : Nat := 2343469737728908489173553

theorem tailTrace_4563891 : CollatzResearch.WordTrace tailWord_4563891 prefixEnd_4563891 2343469737728908489173553 := by
  unfold tailWord_4563891
  simp only [CollatzResearch.WordTrace]
  refine ⟨166458779908809832372683527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110972519939206554915122351 166458779908809832372683527)
  ·
    refine ⟨249688169863214748559025291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166458779908809832372683527 249688169863214748559025291)
    ·
      refine ⟨374532254794822122838537937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249688169863214748559025291 374532254794822122838537937)
      ·
        refine ⟨280899191096116592128903453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374532254794822122838537937 280899191096116592128903453)
        ·
          refine ⟨105337196661043722048338795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 280899191096116592128903453 105337196661043722048338795)
          ·
            refine ⟨158005794991565583072508193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105337196661043722048338795 158005794991565583072508193)
            ·
              refine ⟨118504346243674187304381145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158005794991565583072508193 118504346243674187304381145)
              ·
                refine ⟨88878259682755640478285859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118504346243674187304381145 88878259682755640478285859)
                ·
                  refine ⟨133317389524133460717428789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88878259682755640478285859 133317389524133460717428789)
                  ·
                    refine ⟨12498505267887511942258949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 133317389524133460717428789 12498505267887511942258949)
                    ·
                      refine ⟨2343469737728908489173553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12498505267887511942258949 2343469737728908489173553)
                      ·
                        rfl

theorem cell23_4563891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_4563891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563891 prefixEnd_4563891 := by exact prefixLift 4563891
  have htrace : WordTrace (prefixWord ++ tailWord_4563891) baseStart_4563891 baseEnd_4563891 := by
    simpa [prefixWord, tailWord_4563891, baseEnd_4563891] using wordTrace_append hprefix tailTrace_4563891
  have hstable : (prefixWord ++ tailWord_4563891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563891).length < 2 ^ (prefixWord ++ tailWord_4563891).sum := by decide
  have hdescent : baseEnd_4563891 < baseStart_4563891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563918 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 2, 6]
def baseStart_4563918 : Nat := 118140960795 + 4563918 * 2 ^ 59
def prefixEnd_4563918 : Nat := 4983230072969 + 3 ^ 40 * 4563918 * 2
def baseEnd_4563918 : Nat := 781161200568859961178643

theorem tailTrace_4563918 : CollatzResearch.WordTrace tailWord_4563918 prefixEnd_4563918 781161200568859961178643 := by
  unfold tailWord_4563918
  simp only [CollatzResearch.WordTrace]
  refine ⟨20807470584964001997989551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110973176453141343989277605 20807470584964001997989551)
  ·
    refine ⟨31211205877446002996984327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20807470584964001997989551 31211205877446002996984327)
    ·
      refine ⟨46816808816169004495476491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31211205877446002996984327 46816808816169004495476491)
      ·
        refine ⟨70225213224253506743214737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46816808816169004495476491 70225213224253506743214737)
        ·
          refine ⟨52668909918190130057411053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70225213224253506743214737 52668909918190130057411053)
          ·
            refine ⟨19750841219321298771529145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52668909918190130057411053 19750841219321298771529145)
            ·
              refine ⟨14813130914490974078646859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19750841219321298771529145 14813130914490974078646859)
              ·
                refine ⟨22219696371736461117970289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14813130914490974078646859 22219696371736461117970289)
                ·
                  refine ⟨16664772278802345838477717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22219696371736461117970289 16664772278802345838477717)
                  ·
                    refine ⟨781161200568859961178643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16664772278802345838477717 781161200568859961178643)
                    ·
                      rfl

theorem cell23_4563918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_4563918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563918 prefixEnd_4563918 := by exact prefixLift 4563918
  have htrace : WordTrace (prefixWord ++ tailWord_4563918) baseStart_4563918 baseEnd_4563918 := by
    simpa [prefixWord, tailWord_4563918, baseEnd_4563918] using wordTrace_append hprefix tailTrace_4563918
  have hstable : (prefixWord ++ tailWord_4563918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563918).length < 2 ^ (prefixWord ++ tailWord_4563918).sum := by decide
  have hdescent : baseEnd_4563918 < baseStart_4563918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563970 : List Nat := [3, 4, 1, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_4563970 : Nat := 118140960795 + 4563970 * 2 ^ 59
def prefixEnd_4563970 : Nat := 4983230072969 + 3 ^ 40 * 4563970 * 2
def baseEnd_4563970 : Nat := 2343510302700613680085691

theorem tailTrace_4563970 : CollatzResearch.WordTrace tailWord_4563970 prefixEnd_4563970 2343510302700613680085691 := by
  unfold tailWord_4563970
  simp only [CollatzResearch.WordTrace]
  refine ⟨41615415318880907216202341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110974440850349085909872909 41615415318880907216202341)
  ·
    refine ⟨7802890372290170103037939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41615415318880907216202341 7802890372290170103037939)
    ·
      refine ⟨11704335558435255154556909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7802890372290170103037939 11704335558435255154556909)
      ·
        refine ⟨4389125834413220682958841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11704335558435255154556909 4389125834413220682958841)
        ·
          refine ⟨3291844375809915512219131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4389125834413220682958841 3291844375809915512219131)
          ·
            refine ⟨4937766563714873268328697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3291844375809915512219131 4937766563714873268328697)
            ·
              refine ⟨3703324922786154951246523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4937766563714873268328697 3703324922786154951246523)
              ·
                refine ⟨5554987384179232426869785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3703324922786154951246523 5554987384179232426869785)
                ·
                  refine ⟨4166240538134424320152339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5554987384179232426869785 4166240538134424320152339)
                  ·
                    refine ⟨6249360807201636480228509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4166240538134424320152339 6249360807201636480228509)
                    ·
                      refine ⟨2343510302700613680085691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6249360807201636480228509 2343510302700613680085691)
                      ·
                        rfl

theorem cell23_4563970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_4563970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563970 prefixEnd_4563970 := by exact prefixLift 4563970
  have htrace : WordTrace (prefixWord ++ tailWord_4563970) baseStart_4563970 baseEnd_4563970 := by
    simpa [prefixWord, tailWord_4563970, baseEnd_4563970] using wordTrace_append hprefix tailTrace_4563970
  have hstable : (prefixWord ++ tailWord_4563970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563970).length < 2 ^ (prefixWord ++ tailWord_4563970).sum := by decide
  have hdescent : baseEnd_4563970 < baseStart_4563970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4563976 : List Nat := [2, 1, 3, 2, 1, 5, 2, 1, 2, 2, 2]
def baseStart_4563976 : Nat := 118140960795 + 4563976 * 2 ^ 59
def prefixEnd_4563976 : Nat := 4983230072969 + 3 ^ 40 * 4563976 * 2
def baseEnd_4563976 : Nat := 2343513383584540656610663

theorem tailTrace_4563976 : CollatzResearch.WordTrace tailWord_4563976 prefixEnd_4563976 2343513383584540656610663 := by
  unfold tailWord_4563976
  simp only [CollatzResearch.WordTrace]
  refine ⟨83230940056750945944763891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110974586742334594593018521 83230940056750945944763891)
  ·
    refine ⟨124846410085126418917145837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83230940056750945944763891 124846410085126418917145837)
    ·
      refine ⟨46817403781922407093929689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124846410085126418917145837 46817403781922407093929689)
      ·
        refine ⟨35113052836441805320447267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46817403781922407093929689 35113052836441805320447267)
        ·
          refine ⟨52669579254662707980670901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35113052836441805320447267 52669579254662707980670901)
          ·
            refine ⟨4937773055124628873187897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52669579254662707980670901 4937773055124628873187897)
            ·
              refine ⟨3703329791343471654890923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4937773055124628873187897 3703329791343471654890923)
              ·
                refine ⟨5554994687015207482336385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3703329791343471654890923 5554994687015207482336385)
                ·
                  refine ⟨4166246015261405611752289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5554994687015207482336385 4166246015261405611752289)
                  ·
                    refine ⟨3124684511446054208814217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4166246015261405611752289 3124684511446054208814217)
                    ·
                      refine ⟨2343513383584540656610663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3124684511446054208814217 2343513383584540656610663)
                      ·
                        rfl

theorem cell23_4563976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_4563976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4563976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4563976 prefixEnd_4563976 := by exact prefixLift 4563976
  have htrace : WordTrace (prefixWord ++ tailWord_4563976) baseStart_4563976 baseEnd_4563976 := by
    simpa [prefixWord, tailWord_4563976, baseEnd_4563976] using wordTrace_append hprefix tailTrace_4563976
  have hstable : (prefixWord ++ tailWord_4563976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4563976).length < 2 ^ (prefixWord ++ tailWord_4563976).sum := by decide
  have hdescent : baseEnd_4563976 < baseStart_4563976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4563976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564018 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_4564018 : Nat := 118140960795 + 4564018 * 2 ^ 59
def prefixEnd_4564018 : Nat := 4983230072969 + 3 ^ 40 * 4564018 * 2
def baseEnd_4564018 : Nat := 2343534949772029492285469

theorem tailTrace_4564018 : CollatzResearch.WordTrace tailWord_4564018 prefixEnd_4564018 2343534949772029492285469 := by
  unfold tailWord_4564018
  simp only [CollatzResearch.WordTrace]
  refine ⟨41615852994837433265639177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110975607986233155375037805 41615852994837433265639177)
  ·
    refine ⟨31211889746128074949229383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41615852994837433265639177 31211889746128074949229383)
    ·
      refine ⟨46817834619192112423844075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31211889746128074949229383 46817834619192112423844075)
      ·
        refine ⟨70226751928788168635766113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46817834619192112423844075 70226751928788168635766113)
        ·
          refine ⟨52670063946591126476824585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70226751928788168635766113 52670063946591126476824585)
          ·
            refine ⟨39502547959943344857618439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52670063946591126476824585 39502547959943344857618439)
            ·
              refine ⟨59253821939915017286427659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39502547959943344857618439 59253821939915017286427659)
              ·
                refine ⟨88880732909872525929641489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59253821939915017286427659 88880732909872525929641489)
                ·
                  refine ⟨66660549682404394447231117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88880732909872525929641489 66660549682404394447231117)
                  ·
                    refine ⟨24997706130901647917711669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66660549682404394447231117 24997706130901647917711669)
                    ·
                      refine ⟨2343534949772029492285469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24997706130901647917711669 2343534949772029492285469)
                      ·
                        rfl

theorem cell23_4564018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_4564018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564018 prefixEnd_4564018 := by exact prefixLift 4564018
  have htrace : WordTrace (prefixWord ++ tailWord_4564018) baseStart_4564018 baseEnd_4564018 := by
    simpa [prefixWord, tailWord_4564018, baseEnd_4564018] using wordTrace_append hprefix tailTrace_4564018
  have hstable : (prefixWord ++ tailWord_4564018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564018).length < 2 ^ (prefixWord ++ tailWord_4564018).sum := by decide
  have hdescent : baseEnd_4564018 < baseStart_4564018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564052 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_4564052 : Nat := 118140960795 + 4564052 * 2 ^ 59
def prefixEnd_4564052 : Nat := 4983230072969 + 3 ^ 40 * 4564052 * 2
def baseEnd_4564052 : Nat := 2343552408114282359260313

theorem tailTrace_4564052 : CollatzResearch.WordTrace tailWord_4564052 prefixEnd_4564052 2343552408114282359260313 := by
  unfold tailWord_4564052
  simp only [CollatzResearch.WordTrace]
  refine ⟨83232326030613278434647205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110976434707484371246196273 83232326030613278434647205)
  ·
    refine ⟨15606061130739989706496351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83232326030613278434647205 15606061130739989706496351)
    ·
      refine ⟨23409091696109984559744527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15606061130739989706496351 23409091696109984559744527)
      ·
        refine ⟨35113637544164976839616791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23409091696109984559744527 35113637544164976839616791)
        ·
          refine ⟨52670456316247465259425187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35113637544164976839616791 52670456316247465259425187)
          ·
            refine ⟨79005684474371197889137781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52670456316247465259425187 79005684474371197889137781)
            ·
              refine ⟨7406782919472299802106667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79005684474371197889137781 7406782919472299802106667)
              ·
                refine ⟨11110174379208449703160001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7406782919472299802106667 11110174379208449703160001)
                ·
                  refine ⟨8332630784406337277370001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11110174379208449703160001 8332630784406337277370001)
                  ·
                    refine ⟨6249473088304752958027501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8332630784406337277370001 6249473088304752958027501)
                    ·
                      refine ⟨2343552408114282359260313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6249473088304752958027501 2343552408114282359260313)
                      ·
                        rfl

theorem cell23_4564052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_4564052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564052 prefixEnd_4564052 := by exact prefixLift 4564052
  have htrace : WordTrace (prefixWord ++ tailWord_4564052) baseStart_4564052 baseEnd_4564052 := by
    simpa [prefixWord, tailWord_4564052, baseEnd_4564052] using wordTrace_append hprefix tailTrace_4564052
  have hstable : (prefixWord ++ tailWord_4564052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564052).length < 2 ^ (prefixWord ++ tailWord_4564052).sum := by decide
  have hdescent : baseEnd_4564052 < baseStart_4564052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564072 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 8]
def baseStart_4564072 : Nat := 118140960795 + 4564072 * 2 ^ 59
def prefixEnd_4564072 : Nat := 4983230072969 + 3 ^ 40 * 4564072 * 2
def baseEnd_4564072 : Nat := 260395853080819142334469

theorem tailTrace_4564072 : CollatzResearch.WordTrace tailWord_4564072 prefixEnd_4564072 260395853080819142334469 := by
  unfold tailWord_4564072
  simp only [CollatzResearch.WordTrace]
  refine ⟨83232690760577050142511235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110976921014102733523348313 83232690760577050142511235)
  ·
    refine ⟨124849036140865575213766853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83232690760577050142511235 124849036140865575213766853)
    ·
      refine ⟨23409194276412295352581285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124849036140865575213766853 23409194276412295352581285)
      ·
        refine ⟨4389223926827305378608991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23409194276412295352581285 4389223926827305378608991)
        ·
          refine ⟨6583835890240958067913487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4389223926827305378608991 6583835890240958067913487)
          ·
            refine ⟨9875753835361437101870231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6583835890240958067913487 9875753835361437101870231)
            ·
              refine ⟨14813630753042155652805347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9875753835361437101870231 14813630753042155652805347)
              ·
                refine ⟨22220446129563233479208021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14813630753042155652805347 22220446129563233479208021)
                ·
                  refine ⟨260395853080819142334469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22220446129563233479208021 260395853080819142334469)
                  ·
                    rfl

theorem cell23_4564072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 8].length) (baseStart_4564072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564072 prefixEnd_4564072 := by exact prefixLift 4564072
  have htrace : WordTrace (prefixWord ++ tailWord_4564072) baseStart_4564072 baseEnd_4564072 := by
    simpa [prefixWord, tailWord_4564072, baseEnd_4564072] using wordTrace_append hprefix tailTrace_4564072
  have hstable : (prefixWord ++ tailWord_4564072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564072).length < 2 ^ (prefixWord ++ tailWord_4564072).sum := by decide
  have hdescent : baseEnd_4564072 < baseStart_4564072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564115 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 4, 4]
def baseStart_4564115 : Nat := 118140960795 + 4564115 * 2 ^ 59
def prefixEnd_4564115 : Nat := 4983230072969 + 3 ^ 40 * 4564115 * 2
def baseEnd_4564115 : Nat := 781194919131838537590841

theorem tailTrace_4564115 : CollatzResearch.WordTrace tailWord_4564115 prefixEnd_4564115 781194919131838537590841 := by
  unfold tailWord_4564115
  simp only [CollatzResearch.WordTrace]
  refine ⟨166466949859998318628837799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110977966573332212419225199 166466949859998318628837799)
  ·
    refine ⟨249700424789997477943256699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166466949859998318628837799 249700424789997477943256699)
    ·
      refine ⟨374550637184996216914885049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249700424789997477943256699 374550637184996216914885049)
      ·
        refine ⟨280912977888747162686163787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374550637184996216914885049 280912977888747162686163787)
        ·
          refine ⟨421369466833120744029245681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280912977888747162686163787 421369466833120744029245681)
          ·
            refine ⟨316027100124840558021934261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421369466833120744029245681 316027100124840558021934261)
            ·
              refine ⟨29627540636703802314556337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 316027100124840558021934261 29627540636703802314556337)
              ·
                refine ⟨22220655477527851735917253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29627540636703802314556337 22220655477527851735917253)
                ·
                  refine ⟨4166372902036472200484485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22220655477527851735917253 4166372902036472200484485)
                  ·
                    refine ⟨781194919131838537590841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4166372902036472200484485 781194919131838537590841)
                    ·
                      rfl

theorem cell23_4564115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 4].length) (baseStart_4564115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564115 prefixEnd_4564115 := by exact prefixLift 4564115
  have htrace : WordTrace (prefixWord ++ tailWord_4564115) baseStart_4564115 baseEnd_4564115 := by
    simpa [prefixWord, tailWord_4564115, baseEnd_4564115] using wordTrace_append hprefix tailTrace_4564115
  have hstable : (prefixWord ++ tailWord_4564115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564115).length < 2 ^ (prefixWord ++ tailWord_4564115).sum := by decide
  have hdescent : baseEnd_4564115 < baseStart_4564115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564126 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_4564126 : Nat := 118140960795 + 4564126 * 2 ^ 59
def prefixEnd_4564126 : Nat := 4983230072969 + 3 ^ 40 * 4564126 * 2
def baseEnd_4564126 : Nat := 2343590405682715069734973

theorem tailTrace_4564126 : CollatzResearch.WordTrace tailWord_4564126 prefixEnd_4564126 2343590405682715069734973 := by
  unfold tailWord_4564126
  simp only [CollatzResearch.WordTrace]
  refine ⟨20808418882869808438436029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110978234041972311671658821 20808418882869808438436029)
  ·
    refine ⟨7803157081076178164413511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20808418882869808438436029 7803157081076178164413511)
    ·
      refine ⟨11704735621614267246620267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7803157081076178164413511 11704735621614267246620267)
      ·
        refine ⟨17557103432421400869930401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11704735621614267246620267 17557103432421400869930401)
        ·
          refine ⟨13167827574316050652447801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17557103432421400869930401 13167827574316050652447801)
          ·
            refine ⟨9875870680737037989335851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13167827574316050652447801 9875870680737037989335851)
            ·
              refine ⟨14813806021105556984003777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9875870680737037989335851 14813806021105556984003777)
              ·
                refine ⟨11110354515829167738002833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14813806021105556984003777 11110354515829167738002833)
                ·
                  refine ⟨8332765886871875803502125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11110354515829167738002833 8332765886871875803502125)
                  ·
                    refine ⟨3124787207576953426313297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8332765886871875803502125 3124787207576953426313297)
                    ·
                      refine ⟨2343590405682715069734973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3124787207576953426313297 2343590405682715069734973)
                      ·
                        rfl

theorem cell23_4564126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_4564126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564126 prefixEnd_4564126 := by exact prefixLift 4564126
  have htrace : WordTrace (prefixWord ++ tailWord_4564126) baseStart_4564126 baseEnd_4564126 := by
    simpa [prefixWord, tailWord_4564126, baseEnd_4564126] using wordTrace_append hprefix tailTrace_4564126
  have hstable : (prefixWord ++ tailWord_4564126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564126).length < 2 ^ (prefixWord ++ tailWord_4564126).sum := by decide
  have hdescent : baseEnd_4564126 < baseStart_4564126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564132 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 4, 4]
def baseStart_4564132 : Nat := 118140960795 + 4564132 * 2 ^ 59
def prefixEnd_4564132 : Nat := 4983230072969 + 3 ^ 40 * 4564132 * 2
def baseEnd_4564132 : Nat := 781197828855547348753315

theorem tailTrace_4564132 : CollatzResearch.WordTrace tailWord_4564132 prefixEnd_4564132 781197828855547348753315 := by
  unfold tailWord_4564132
  simp only [CollatzResearch.WordTrace]
  refine ⟨83233784950468365266103325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110978379933957820354804433 83233784950468365266103325)
  ·
    refine ⟨31212669356425636974788747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83233784950468365266103325 31212669356425636974788747)
    ·
      refine ⟨46819004034638455462183121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31212669356425636974788747 46819004034638455462183121)
      ·
        refine ⟨35114253025978841596637341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46819004034638455462183121 35114253025978841596637341)
        ·
          refine ⟨13167844884742065598739003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35114253025978841596637341 13167844884742065598739003)
          ·
            refine ⟨19751767327113098398108505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13167844884742065598739003 19751767327113098398108505)
            ·
              refine ⟨14813825495334823798581379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19751767327113098398108505 14813825495334823798581379)
              ·
                refine ⟨22220738243002235697872069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14813825495334823798581379 22220738243002235697872069)
                ·
                  refine ⟨4166388420562919193351013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22220738243002235697872069 4166388420562919193351013)
                  ·
                    refine ⟨781197828855547348753315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4166388420562919193351013 781197828855547348753315)
                    ·
                      rfl

theorem cell23_4564132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_4564132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564132 prefixEnd_4564132 := by exact prefixLift 4564132
  have htrace : WordTrace (prefixWord ++ tailWord_4564132) baseStart_4564132 baseEnd_4564132 := by
    simpa [prefixWord, tailWord_4564132, baseEnd_4564132] using wordTrace_append hprefix tailTrace_4564132
  have hstable : (prefixWord ++ tailWord_4564132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564132).length < 2 ^ (prefixWord ++ tailWord_4564132).sum := by decide
  have hdescent : baseEnd_4564132 < baseStart_4564132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564145 : List Nat := [1, 2, 2, 5, 1, 1, 1, 10]
def baseStart_4564145 : Nat := 118140960795 + 4564145 * 2 ^ 59
def prefixEnd_4564145 : Nat := 4983230072969 + 3 ^ 40 * 4564145 * 2
def baseEnd_4564145 : Nat := 86800005993153722051755

theorem tailTrace_4564145 : CollatzResearch.WordTrace tailWord_4564145 prefixEnd_4564145 86800005993153722051755 := by
  unfold tailWord_4564145
  simp only [CollatzResearch.WordTrace]
  refine ⟨166468044049889633752429889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110978696033259755834953259 166468044049889633752429889)
  ·
    refine ⟨124851033037417225314322417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166468044049889633752429889 124851033037417225314322417)
    ·
      refine ⟨93638274778062918985741813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124851033037417225314322417 93638274778062918985741813)
      ·
        refine ⟨8778588260443398654913295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93638274778062918985741813 8778588260443398654913295)
        ·
          refine ⟨13167882390665097982369943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8778588260443398654913295 13167882390665097982369943)
          ·
            refine ⟨19751823585997646973554915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13167882390665097982369943 19751823585997646973554915)
            ·
              refine ⟨29627735378996470460332373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19751823585997646973554915 29627735378996470460332373)
              ·
                refine ⟨86800005993153722051755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29627735378996470460332373 86800005993153722051755)
                ·
                  rfl

theorem cell23_4564145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 10].length) (baseStart_4564145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564145 prefixEnd_4564145 := by exact prefixLift 4564145
  have htrace : WordTrace (prefixWord ++ tailWord_4564145) baseStart_4564145 baseEnd_4564145 := by
    simpa [prefixWord, tailWord_4564145, baseEnd_4564145] using wordTrace_append hprefix tailTrace_4564145
  have hstable : (prefixWord ++ tailWord_4564145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564145).length < 2 ^ (prefixWord ++ tailWord_4564145).sum := by decide
  have hdescent : baseEnd_4564145 < baseStart_4564145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564229 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 4, 2, 2]
def baseStart_4564229 : Nat := 118140960795 + 4564229 * 2 ^ 59
def prefixEnd_4564229 : Nat := 4983230072969 + 3 ^ 40 * 4564229 * 2
def baseEnd_4564229 : Nat := 2343643294190128166746999

theorem tailTrace_4564229 : CollatzResearch.WordTrace tailWord_4564229 prefixEnd_4564229 2343643294190128166746999 := by
  unfold tailWord_4564229
  simp only [CollatzResearch.WordTrace]
  refine ⟨166471107781585316098487741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110980738521056877398991827 166471107781585316098487741)
  ·
    refine ⟨62426665418094493536932903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166471107781585316098487741 62426665418094493536932903)
    ·
      refine ⟨93639998127141740305399355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62426665418094493536932903 93639998127141740305399355)
      ·
        refine ⟨140459997190712610458099033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93639998127141740305399355 140459997190712610458099033)
        ·
          refine ⟨105344997893034457843574275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140459997190712610458099033 105344997893034457843574275)
          ·
            refine ⟨158017496839551686765361413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105344997893034457843574275 158017496839551686765361413)
            ·
              refine ⟨29628280657415941268505265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158017496839551686765361413 29628280657415941268505265)
              ·
                refine ⟨22221210493061955951378949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29628280657415941268505265 22221210493061955951378949)
                ·
                  refine ⟨4166476967449116740883553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22221210493061955951378949 4166476967449116740883553)
                  ·
                    refine ⟨3124857725586837555662665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4166476967449116740883553 3124857725586837555662665)
                    ·
                      refine ⟨2343643294190128166746999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3124857725586837555662665 2343643294190128166746999)
                      ·
                        rfl

theorem cell23_4564229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 2, 2].length) (baseStart_4564229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564229 prefixEnd_4564229 := by exact prefixLift 4564229
  have htrace : WordTrace (prefixWord ++ tailWord_4564229) baseStart_4564229 baseEnd_4564229 := by
    simpa [prefixWord, tailWord_4564229, baseEnd_4564229] using wordTrace_append hprefix tailTrace_4564229
  have hstable : (prefixWord ++ tailWord_4564229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564229).length < 2 ^ (prefixWord ++ tailWord_4564229).sum := by decide
  have hdescent : baseEnd_4564229 < baseStart_4564229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564269 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 7]
def baseStart_4564269 : Nat := 118140960795 + 4564269 * 2 ^ 59
def prefixEnd_4564269 : Nat := 4983230072969 + 3 ^ 40 * 4564269 * 2
def baseEnd_4564269 : Nat := 260407092601812001138535

theorem tailTrace_4564269 : CollatzResearch.WordTrace tailWord_4564269 prefixEnd_4564269 260407092601812001138535 := by
  unfold tailWord_4564269
  simp only [CollatzResearch.WordTrace]
  refine ⟨166472566701440402929943861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110981711134293601953295907 166472566701440402929943861)
  ·
    refine ⟨15606803128260037774682237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166472566701440402929943861 15606803128260037774682237)
    ·
      refine ⟨5852551173097514165505839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15606803128260037774682237 5852551173097514165505839)
      ·
        refine ⟨8778826759646271248258759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5852551173097514165505839 8778826759646271248258759)
        ·
          refine ⟨13168240139469406872388139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8778826759646271248258759 13168240139469406872388139)
          ·
            refine ⟨19752360209204110308582209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13168240139469406872388139 19752360209204110308582209)
            ·
              refine ⟨14814270156903082731436657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19752360209204110308582209 14814270156903082731436657)
              ·
                refine ⟨11110702617677312048577493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14814270156903082731436657 11110702617677312048577493)
                ·
                  refine ⟨260407092601812001138535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11110702617677312048577493 260407092601812001138535)
                  ·
                    rfl

theorem cell23_4564269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_4564269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564269 prefixEnd_4564269 := by exact prefixLift 4564269
  have htrace : WordTrace (prefixWord ++ tailWord_4564269) baseStart_4564269 baseEnd_4564269 := by
    simpa [prefixWord, tailWord_4564269, baseEnd_4564269] using wordTrace_append hprefix tailTrace_4564269
  have hstable : (prefixWord ++ tailWord_4564269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564269).length < 2 ^ (prefixWord ++ tailWord_4564269).sum := by decide
  have hdescent : baseEnd_4564269 < baseStart_4564269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564282 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 2, 5]
def baseStart_4564282 : Nat := 118140960795 + 4564282 * 2 ^ 59
def prefixEnd_4564282 : Nat := 4983230072969 + 3 ^ 40 * 4564282 * 2
def baseEnd_4564282 : Nat := 781223502888272153128085

theorem tailTrace_4564282 : CollatzResearch.WordTrace tailWord_4564282 prefixEnd_4564282 781223502888272153128085 := by
  unfold tailWord_4564282
  simp only [CollatzResearch.WordTrace]
  refine ⟨41618260212598326537541775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110982027233595537433444733 41618260212598326537541775)
  ·
    refine ⟨62427390318897489806312663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41618260212598326537541775 62427390318897489806312663)
    ·
      refine ⟨93641085478346234709468995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62427390318897489806312663 93641085478346234709468995)
      ·
        refine ⟨140461628217519352064203493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93641085478346234709468995 140461628217519352064203493)
        ·
          refine ⟨26336555290784878512038155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140461628217519352064203493 26336555290784878512038155)
          ·
            refine ⟨39504832936177317768057233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26336555290784878512038155 39504832936177317768057233)
            ·
              refine ⟨29628624702132988326042925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39504832936177317768057233 29628624702132988326042925)
              ·
                refine ⟨11110734263299870622266097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29628624702132988326042925 11110734263299870622266097)
                ·
                  refine ⟨8333050697474902966699573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11110734263299870622266097 8333050697474902966699573)
                  ·
                    refine ⟨781223502888272153128085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8333050697474902966699573 781223502888272153128085)
                    ·
                      rfl

theorem cell23_4564282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_4564282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564282 prefixEnd_4564282 := by exact prefixLift 4564282
  have htrace : WordTrace (prefixWord ++ tailWord_4564282) baseStart_4564282 baseEnd_4564282 := by
    simpa [prefixWord, tailWord_4564282, baseEnd_4564282] using wordTrace_append hprefix tailTrace_4564282
  have hstable : (prefixWord ++ tailWord_4564282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564282).length < 2 ^ (prefixWord ++ tailWord_4564282).sum := by decide
  have hdescent : baseEnd_4564282 < baseStart_4564282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564359 : List Nat := [1, 1, 4, 2, 2, 3, 2, 2, 6]
def baseStart_4564359 : Nat := 118140960795 + 4564359 * 2 ^ 59
def prefixEnd_4564359 : Nat := 4983230072969 + 3 ^ 40 * 4564359 * 2
def baseEnd_4564359 : Nat := 260412227408356962013489

theorem tailTrace_4564359 : CollatzResearch.WordTrace tailWord_4564359 prefixEnd_4564359 260412227408356962013489 := by
  unfold tailWord_4564359
  simp only [CollatzResearch.WordTrace]
  refine ⟨166475849271114348300720131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110983899514076232200480087 166475849271114348300720131)
  ·
    refine ⟨249713773906671522451080197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166475849271114348300720131 249713773906671522451080197)
    ·
      refine ⟨46821332607500910459577537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 249713773906671522451080197 46821332607500910459577537)
      ·
        refine ⟨35115999455625682844683153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46821332607500910459577537 35115999455625682844683153)
        ·
          refine ⟨26336999591719262133512365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35115999455625682844683153 26336999591719262133512365)
          ·
            refine ⟨9876374846894723300067137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26336999591719262133512365 9876374846894723300067137)
            ·
              refine ⟨7407281135171042475050353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9876374846894723300067137 7407281135171042475050353)
              ·
                refine ⟨5555460851378281856287765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7407281135171042475050353 5555460851378281856287765)
                ·
                  refine ⟨260412227408356962013489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5555460851378281856287765 260412227408356962013489)
                  ·
                    rfl

theorem cell23_4564359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 6].length) (baseStart_4564359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564359 prefixEnd_4564359 := by exact prefixLift 4564359
  have htrace : WordTrace (prefixWord ++ tailWord_4564359) baseStart_4564359 baseEnd_4564359 := by
    simpa [prefixWord, tailWord_4564359, baseEnd_4564359] using wordTrace_append hprefix tailTrace_4564359
  have hstable : (prefixWord ++ tailWord_4564359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564359).length < 2 ^ (prefixWord ++ tailWord_4564359).sum := by decide
  have hdescent : baseEnd_4564359 < baseStart_4564359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564386 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_4564386 : Nat := 118140960795 + 4564386 * 2 ^ 59
def prefixEnd_4564386 : Nat := 4983230072969 + 3 ^ 40 * 4564386 * 2
def baseEnd_4564386 : Nat := 2343723910652884052483777

theorem tailTrace_4564386 : CollatzResearch.WordTrace tailWord_4564386 prefixEnd_4564386 2343723910652884052483777 := by
  unfold tailWord_4564386
  simp only [CollatzResearch.WordTrace]
  refine ⟨41619208510504132977988253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110984556028011021274635341 41619208510504132977988253)
  ·
    refine ⟨15607203191439049866745595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41619208510504132977988253 15607203191439049866745595)
    ·
      refine ⟨23410804787158574800118393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15607203191439049866745595 23410804787158574800118393)
      ·
        refine ⟨17558103590368931100088795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23410804787158574800118393 17558103590368931100088795)
        ·
          refine ⟨26337155385553396650133193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17558103590368931100088795 26337155385553396650133193)
          ·
            refine ⟨19752866539165047487599895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26337155385553396650133193 19752866539165047487599895)
            ·
              refine ⟨29629299808747571231399843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19752866539165047487599895 29629299808747571231399843)
              ·
                refine ⟨44443949713121356847099765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29629299808747571231399843 44443949713121356847099765)
                ·
                  refine ⟨4166620285605127204415603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44443949713121356847099765 4166620285605127204415603)
                  ·
                    refine ⟨6249930428407690806623405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4166620285605127204415603 6249930428407690806623405)
                    ·
                      refine ⟨2343723910652884052483777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6249930428407690806623405 2343723910652884052483777)
                      ·
                        rfl

theorem cell23_4564386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_4564386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564386 prefixEnd_4564386 := by exact prefixLift 4564386
  have htrace : WordTrace (prefixWord ++ tailWord_4564386) baseStart_4564386 baseEnd_4564386 := by
    simpa [prefixWord, tailWord_4564386, baseEnd_4564386] using wordTrace_append hprefix tailTrace_4564386
  have hstable : (prefixWord ++ tailWord_4564386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564386).length < 2 ^ (prefixWord ++ tailWord_4564386).sum := by decide
  have hdescent : baseEnd_4564386 < baseStart_4564386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564396 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 2, 3, 2]
def baseStart_4564396 : Nat := 118140960795 + 4564396 * 2 ^ 59
def prefixEnd_4564396 : Nat := 4983230072969 + 3 ^ 40 * 4564396 * 2
def baseEnd_4564396 : Nat := 2343729045459429013358731

theorem tailTrace_4564396 : CollatzResearch.WordTrace tailWord_4564396 prefixEnd_4564396 2343729045459429013358731 := by
  unfold tailWord_4564396
  simp only [CollatzResearch.WordTrace]
  refine ⟨83238599385990151809908521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110984799181320202413211361 83238599385990151809908521)
  ·
    refine ⟨62428949539492613857431391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83238599385990151809908521 62428949539492613857431391)
    ·
      refine ⟨93643424309238920786147087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62428949539492613857431391 93643424309238920786147087)
      ·
        refine ⟨140465136463858381179220631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93643424309238920786147087 140465136463858381179220631)
        ·
          refine ⟨210697704695787571768830947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140465136463858381179220631 210697704695787571768830947)
          ·
            refine ⟨316046557043681357653246421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210697704695787571768830947 316046557043681357653246421)
            ·
              refine ⟨7407341180711281819997963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 316046557043681357653246421 7407341180711281819997963)
              ·
                refine ⟨11111011771066922729996945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7407341180711281819997963 11111011771066922729996945)
                ·
                  refine ⟨8333258828300192047497709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11111011771066922729996945 8333258828300192047497709)
                  ·
                    refine ⟨3124972060612572017811641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8333258828300192047497709 3124972060612572017811641)
                    ·
                      refine ⟨2343729045459429013358731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3124972060612572017811641 2343729045459429013358731)
                      ·
                        rfl

theorem cell23_4564396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 3, 2].length) (baseStart_4564396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564396 prefixEnd_4564396 := by exact prefixLift 4564396
  have htrace : WordTrace (prefixWord ++ tailWord_4564396) baseStart_4564396 baseEnd_4564396 := by
    simpa [prefixWord, tailWord_4564396, baseEnd_4564396] using wordTrace_append hprefix tailTrace_4564396
  have hstable : (prefixWord ++ tailWord_4564396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564396).length < 2 ^ (prefixWord ++ tailWord_4564396).sum := by decide
  have hdescent : baseEnd_4564396 < baseStart_4564396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564402 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 3, 6]
def baseStart_4564402 : Nat := 118140960795 + 4564402 * 2 ^ 59
def prefixEnd_4564402 : Nat := 4983230072969 + 3 ^ 40 * 4564402 * 2
def baseEnd_4564402 : Nat := 781244042114451996627901

theorem tailTrace_4564402 : CollatzResearch.WordTrace tailWord_4564402 prefixEnd_4564402 781244042114451996627901 := by
  unfold tailWord_4564402
  simp only [CollatzResearch.WordTrace]
  refine ⟨41619354402489641661133865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110984945073305711096356973 41619354402489641661133865)
  ·
    refine ⟨31214515801867231245850399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41619354402489641661133865 31214515801867231245850399)
    ·
      refine ⟨46821773702800846868775599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31214515801867231245850399 46821773702800846868775599)
      ·
        refine ⟨70232660554201270303163399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46821773702800846868775599 70232660554201270303163399)
        ·
          refine ⟨105348990831301905454745099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70232660554201270303163399 105348990831301905454745099)
          ·
            refine ⟨158023486246952858182117649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105348990831301905454745099 158023486246952858182117649)
            ·
              refine ⟨118517614685214643636588237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158023486246952858182117649 118517614685214643636588237)
              ·
                refine ⟨44444105506955491363720589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118517614685214643636588237 44444105506955491363720589)
                ·
                  refine ⟨16666539565108309261395221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44444105506955491363720589 16666539565108309261395221)
                  ·
                    refine ⟨781244042114451996627901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16666539565108309261395221 781244042114451996627901)
                    ·
                      rfl

theorem cell23_4564402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_4564402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564402 prefixEnd_4564402 := by exact prefixLift 4564402
  have htrace : WordTrace (prefixWord ++ tailWord_4564402) baseStart_4564402 baseEnd_4564402 := by
    simpa [prefixWord, tailWord_4564402, baseEnd_4564402] using wordTrace_append hprefix tailTrace_4564402
  have hstable : (prefixWord ++ tailWord_4564402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564402).length < 2 ^ (prefixWord ++ tailWord_4564402).sum := by decide
  have hdescent : baseEnd_4564402 < baseStart_4564402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564420 : List Nat := [2, 3, 3, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_4564420 : Nat := 118140960795 + 4564420 * 2 ^ 59
def prefixEnd_4564420 : Nat := 4983230072969 + 3 ^ 40 * 4564420 * 2
def baseEnd_4564420 : Nat := 2343741368995136919458621

theorem tailTrace_4564420 : CollatzResearch.WordTrace tailWord_4564420 prefixEnd_4564420 2343741368995136919458621 := by
  unfold tailWord_4564420
  simp only [CollatzResearch.WordTrace]
  refine ⟨83239037061946677859345357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110985382749262237145793809 83239037061946677859345357)
  ·
    refine ⟨31214638898230004197254509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83239037061946677859345357 31214638898230004197254509)
    ·
      refine ⟨11705489586836251573970441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31214638898230004197254509 11705489586836251573970441)
      ·
        refine ⟨8779117190127188680477831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11705489586836251573970441 8779117190127188680477831)
        ·
          refine ⟨13168675785190783020716747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8779117190127188680477831 13168675785190783020716747)
          ·
            refine ⟨19753013677786174531075121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13168675785190783020716747 19753013677786174531075121)
            ·
              refine ⟨14814760258339630898306341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19753013677786174531075121 14814760258339630898306341)
              ·
                refine ⟨2777767548438680793432439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14814760258339630898306341 2777767548438680793432439)
                ·
                  refine ⟨4166651322658021190148659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2777767548438680793432439 4166651322658021190148659)
                  ·
                    refine ⟨6249976983987031785222989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4166651322658021190148659 6249976983987031785222989)
                    ·
                      refine ⟨2343741368995136919458621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6249976983987031785222989 2343741368995136919458621)
                      ·
                        rfl

theorem cell23_4564420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_4564420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564420 prefixEnd_4564420 := by exact prefixLift 4564420
  have htrace : WordTrace (prefixWord ++ tailWord_4564420) baseStart_4564420 baseEnd_4564420 := by
    simpa [prefixWord, tailWord_4564420, baseEnd_4564420] using wordTrace_append hprefix tailTrace_4564420
  have hstable : (prefixWord ++ tailWord_4564420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564420).length < 2 ^ (prefixWord ++ tailWord_4564420).sum := by decide
  have hdescent : baseEnd_4564420 < baseStart_4564420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564449 : List Nat := [1, 2, 3, 1, 2, 3, 4, 7]
def baseStart_4564449 : Nat := 118140960795 + 4564449 * 2 ^ 59
def prefixEnd_4564449 : Nat := 4983230072969 + 3 ^ 40 * 4564449 * 2
def baseEnd_4564449 : Nat := 86805787404967307629481

theorem tailTrace_4564449 : CollatzResearch.WordTrace tailWord_4564449 prefixEnd_4564449 86805787404967307629481 := by
  unfold tailWord_4564449
  simp only [CollatzResearch.WordTrace]
  refine ⟨166479131840788293671496401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110986087893858862447664267 166479131840788293671496401)
  ·
    refine ⟨124859348880591220253622301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166479131840788293671496401 124859348880591220253622301)
    ·
      refine ⟨46822255830221707595108363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124859348880591220253622301 46822255830221707595108363)
      ·
        refine ⟨70233383745332561392662545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46822255830221707595108363 70233383745332561392662545)
        ·
          refine ⟨52675037808999421044496909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70233383745332561392662545 52675037808999421044496909)
          ·
            refine ⟨19753139178374782891686341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52675037808999421044496909 19753139178374782891686341)
            ·
              refine ⟨3703713595945271792191189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19753139178374782891686341 3703713595945271792191189)
              ·
                refine ⟨86805787404967307629481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3703713595945271792191189 86805787404967307629481)
                ·
                  rfl

theorem cell23_4564449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 7].length) (baseStart_4564449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564449 prefixEnd_4564449 := by exact prefixLift 4564449
  have htrace : WordTrace (prefixWord ++ tailWord_4564449) baseStart_4564449 baseEnd_4564449 := by
    simpa [prefixWord, tailWord_4564449, baseEnd_4564449] using wordTrace_append hprefix tailTrace_4564449
  have hstable : (prefixWord ++ tailWord_4564449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564449).length < 2 ^ (prefixWord ++ tailWord_4564449).sum := by decide
  have hdescent : baseEnd_4564449 < baseStart_4564449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564452 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_4564452 : Nat := 118140960795 + 4564452 * 2 ^ 59
def prefixEnd_4564452 : Nat := 4983230072969 + 3 ^ 40 * 4564452 * 2
def baseEnd_4564452 : Nat := 2343757800376080794258473

theorem tailTrace_4564452 : CollatzResearch.WordTrace tailWord_4564452 prefixEnd_4564452 2343757800376080794258473 := by
  unfold tailWord_4564452
  simp only [CollatzResearch.WordTrace]
  refine ⟨83239620629888712591927805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110986160839851616789237073 83239620629888712591927805)
  ·
    refine ⟨31214857736208267221972927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83239620629888712591927805 31214857736208267221972927)
    ·
      refine ⟨46822286604312400832959391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31214857736208267221972927 46822286604312400832959391)
      ·
        refine ⟨70233429906468601249439087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46822286604312400832959391 70233429906468601249439087)
        ·
          refine ⟨105350144859702901874158631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70233429906468601249439087 105350144859702901874158631)
          ·
            refine ⟨158025217289554352811237947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105350144859702901874158631 158025217289554352811237947)
            ·
              refine ⟨237037825934331529216856921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158025217289554352811237947 237037825934331529216856921)
              ·
                refine ⟨177778369450748646912642691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 237037825934331529216856921 177778369450748646912642691)
                ·
                  refine ⟨266667554176122970368964037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177778369450748646912642691 266667554176122970368964037)
                  ·
                    refine ⟨50000166408023056944180757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 266667554176122970368964037 50000166408023056944180757)
                    ·
                      refine ⟨2343757800376080794258473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50000166408023056944180757 2343757800376080794258473)
                      ·
                        rfl

theorem cell23_4564452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_4564452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564452 prefixEnd_4564452 := by exact prefixLift 4564452
  have htrace : WordTrace (prefixWord ++ tailWord_4564452) baseStart_4564452 baseEnd_4564452 := by
    simpa [prefixWord, tailWord_4564452, baseEnd_4564452] using wordTrace_append hprefix tailTrace_4564452
  have hstable : (prefixWord ++ tailWord_4564452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564452).length < 2 ^ (prefixWord ++ tailWord_4564452).sum := by decide
  have hdescent : baseEnd_4564452 < baseStart_4564452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564476 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 4, 1, 3]
def baseStart_4564476 : Nat := 118140960795 + 4564476 * 2 ^ 59
def prefixEnd_4564476 : Nat := 4983230072969 + 3 ^ 40 * 4564476 * 2
def baseEnd_4564476 : Nat := 2343770123911788700358363

theorem tailTrace_4564476 : CollatzResearch.WordTrace tailWord_4564476 prefixEnd_4564476 2343770123911788700358363 := by
  unfold tailWord_4564476
  simp only [CollatzResearch.WordTrace]
  refine ⟨83240058305845238641364641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110986744407793651521819521 83240058305845238641364641)
  ·
    refine ⟨62430043729383928981023481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83240058305845238641364641 62430043729383928981023481)
    ·
      refine ⟨46822532797037946735767611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62430043729383928981023481 46822532797037946735767611)
      ·
        refine ⟨70233799195556920103651417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46822532797037946735767611 70233799195556920103651417)
        ·
          refine ⟨52675349396667690077738563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70233799195556920103651417 52675349396667690077738563)
          ·
            refine ⟨79013024095001535116607845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52675349396667690077738563 79013024095001535116607845)
            ·
              refine ⟨14814942017812787834363971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79013024095001535116607845 14814942017812787834363971)
              ·
                refine ⟨22222413026719181751545957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14814942017812787834363971 22222413026719181751545957)
                ·
                  refine ⟨4166702442509846578414867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22222413026719181751545957 4166702442509846578414867)
                  ·
                    refine ⟨6250053663764769867622301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4166702442509846578414867 6250053663764769867622301)
                    ·
                      refine ⟨2343770123911788700358363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6250053663764769867622301 2343770123911788700358363)
                      ·
                        rfl

theorem cell23_4564476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_4564476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564476 prefixEnd_4564476 := by exact prefixLift 4564476
  have htrace : WordTrace (prefixWord ++ tailWord_4564476) baseStart_4564476 baseEnd_4564476 := by
    simpa [prefixWord, tailWord_4564476, baseEnd_4564476] using wordTrace_append hprefix tailTrace_4564476
  have hstable : (prefixWord ++ tailWord_4564476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564476).length < 2 ^ (prefixWord ++ tailWord_4564476).sum := by decide
  have hdescent : baseEnd_4564476 < baseStart_4564476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564477 : List Nat := [1, 4, 1, 1, 1, 5, 3, 2, 1, 2, 2]
def baseStart_4564477 : Nat := 118140960795 + 4564477 * 2 ^ 59
def prefixEnd_4564477 : Nat := 4983230072969 + 3 ^ 40 * 4564477 * 2
def baseEnd_4564477 : Nat := 2343770637392443196445859

theorem tailTrace_4564477 : CollatzResearch.WordTrace tailWord_4564477 prefixEnd_4564477 2343770637392443196445859 := by
  unfold tailWord_4564477
  simp only [CollatzResearch.WordTrace]
  refine ⟨166480153084686854453515685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110986768723124569635677123 166480153084686854453515685)
  ·
    refine ⟨31215028703378785210034191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166480153084686854453515685 31215028703378785210034191)
    ·
      refine ⟨46822543055068177815051287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31215028703378785210034191 46822543055068177815051287)
      ·
        refine ⟨70233814582602266722576931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46822543055068177815051287 70233814582602266722576931)
        ·
          refine ⟨105350721873903400083865397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70233814582602266722576931 105350721873903400083865397)
          ·
            refine ⟨9876630175678443757862381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105350721873903400083865397 9876630175678443757862381)
            ·
              refine ⟨3703736315879416409198393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9876630175678443757862381 3703736315879416409198393)
              ·
                refine ⟨2777802236909562306898795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3703736315879416409198393 2777802236909562306898795)
                ·
                  refine ⟨4166703355364343460348193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2777802236909562306898795 4166703355364343460348193)
                  ·
                    refine ⟨3125027516523257595261145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4166703355364343460348193 3125027516523257595261145)
                    ·
                      refine ⟨2343770637392443196445859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3125027516523257595261145 2343770637392443196445859)
                      ·
                        rfl

theorem cell23_4564477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_4564477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564477 prefixEnd_4564477 := by exact prefixLift 4564477
  have htrace : WordTrace (prefixWord ++ tailWord_4564477) baseStart_4564477 baseEnd_4564477 := by
    simpa [prefixWord, tailWord_4564477, baseEnd_4564477] using wordTrace_append hprefix tailTrace_4564477
  have hstable : (prefixWord ++ tailWord_4564477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564477).length < 2 ^ (prefixWord ++ tailWord_4564477).sum := by decide
  have hdescent : baseEnd_4564477 < baseStart_4564477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564529 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 2, 2, 4]
def baseStart_4564529 : Nat := 118140960795 + 4564529 * 2 ^ 59
def prefixEnd_4564529 : Nat := 4983230072969 + 3 ^ 40 * 4564529 * 2
def baseEnd_4564529 : Nat := 2343797338386476992995619

theorem tailTrace_4564529 : CollatzResearch.WordTrace tailWord_4564529 prefixEnd_4564529 2343797338386476992995619 := by
  unfold tailWord_4564529
  simp only [CollatzResearch.WordTrace]
  refine ⟨166482049680498467334408641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110988033120332311556272427 166482049680498467334408641)
  ·
    refine ⟨124861537260373850500806481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166482049680498467334408641 124861537260373850500806481)
    ·
      refine ⟨93646152945280387875604861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124861537260373850500806481 93646152945280387875604861)
      ·
        refine ⟨35117307354480145453351823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93646152945280387875604861 35117307354480145453351823)
        ·
          refine ⟨52675961031720218180027735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35117307354480145453351823 52675961031720218180027735)
          ·
            refine ⟨79013941547580327270041603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52675961031720218180027735 79013941547580327270041603)
            ·
              refine ⟨118520912321370490905062405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79013941547580327270041603 118520912321370490905062405)
              ·
                refine ⟨22222671060256967044699201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118520912321370490905062405 22222671060256967044699201)
                ·
                  refine ⟨16667003295192725283524401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22222671060256967044699201 16667003295192725283524401)
                  ·
                    refine ⟨12500252471394543962643301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16667003295192725283524401 12500252471394543962643301)
                    ·
                      refine ⟨2343797338386476992995619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12500252471394543962643301 2343797338386476992995619)
                      ·
                        rfl

theorem cell23_4564529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_4564529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564529 prefixEnd_4564529 := by exact prefixLift 4564529
  have htrace : WordTrace (prefixWord ++ tailWord_4564529) baseStart_4564529 baseEnd_4564529 := by
    simpa [prefixWord, tailWord_4564529, baseEnd_4564529] using wordTrace_append hprefix tailTrace_4564529
  have hstable : (prefixWord ++ tailWord_4564529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564529).length < 2 ^ (prefixWord ++ tailWord_4564529).sum := by decide
  have hdescent : baseEnd_4564529 < baseStart_4564529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564619 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 4]
def baseStart_4564619 : Nat := 118140960795 + 4564619 * 2 ^ 59
def prefixEnd_4564619 : Nat := 4983230072969 + 3 ^ 40 * 4564619 * 2
def baseEnd_4564619 : Nat := 2343843551645381640870205

theorem tailTrace_4564619 : CollatzResearch.WordTrace tailWord_4564619 prefixEnd_4564619 2343843551645381640870205 := by
  unfold tailWord_4564619
  simp only [CollatzResearch.WordTrace]
  refine ⟨166485332250172412705184911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110990221500114941803456607 166485332250172412705184911)
  ·
    refine ⟨249727998375258619057777367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166485332250172412705184911 249727998375258619057777367)
    ·
      refine ⟨374591997562887928586666051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249727998375258619057777367 374591997562887928586666051)
      ·
        refine ⟨561887996344331892879999077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374591997562887928586666051 561887996344331892879999077)
        ·
          refine ⟨105353999314562229914999827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 561887996344331892879999077 105353999314562229914999827)
          ·
            refine ⟨158030998971843344872499741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105353999314562229914999827 158030998971843344872499741)
            ·
              refine ⟨59261624614441254327187403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158030998971843344872499741 59261624614441254327187403)
              ·
                refine ⟨88892436921661881490781105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59261624614441254327187403 88892436921661881490781105)
                ·
                  refine ⟨66669327691246411118085829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88892436921661881490781105 66669327691246411118085829)
                  ·
                    refine ⟨12500498942108702084641093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66669327691246411118085829 12500498942108702084641093)
                    ·
                      refine ⟨2343843551645381640870205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12500498942108702084641093 2343843551645381640870205)
                      ·
                        rfl

theorem cell23_4564619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 4].length) (baseStart_4564619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564619 prefixEnd_4564619 := by exact prefixLift 4564619
  have htrace : WordTrace (prefixWord ++ tailWord_4564619) baseStart_4564619 baseEnd_4564619 := by
    simpa [prefixWord, tailWord_4564619, baseEnd_4564619] using wordTrace_append hprefix tailTrace_4564619
  have hstable : (prefixWord ++ tailWord_4564619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564619).length < 2 ^ (prefixWord ++ tailWord_4564619).sum := by decide
  have hdescent : baseEnd_4564619 < baseStart_4564619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564633 : List Nat := [1, 2, 1, 2, 1, 2, 2, 7, 1, 4]
def baseStart_4564633 : Nat := 118140960795 + 4564633 * 2 ^ 59
def prefixEnd_4564633 : Nat := 4983230072969 + 3 ^ 40 * 4564633 * 2
def baseEnd_4564633 : Nat := 781283580124848195365047

theorem tailTrace_4564633 : CollatzResearch.WordTrace tailWord_4564633 prefixEnd_4564633 781283580124848195365047 := by
  unfold tailWord_4564633
  simp only [CollatzResearch.WordTrace]
  refine ⟨166485842872121693096194553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110990561914747795397463035 166485842872121693096194553)
  ·
    refine ⟨124864382154091269822145915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166485842872121693096194553 124864382154091269822145915)
    ·
      refine ⟨187296573231136904733218873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124864382154091269822145915 187296573231136904733218873)
      ·
        refine ⟨140472429923352678549914155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187296573231136904733218873 140472429923352678549914155)
        ·
          refine ⟨210708644885029017824871233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140472429923352678549914155 210708644885029017824871233)
          ·
            refine ⟨158031483663771763368653425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210708644885029017824871233 158031483663771763368653425)
            ·
              refine ⟨118523612747828822526490069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158031483663771763368653425 118523612747828822526490069)
              ·
                refine ⟨2777897173777238027964611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 118523612747828822526490069 2777897173777238027964611)
                ·
                  refine ⟨4166845760665857041946917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2777897173777238027964611 4166845760665857041946917)
                  ·
                    refine ⟨781283580124848195365047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4166845760665857041946917 781283580124848195365047)
                    ·
                      rfl

theorem cell23_4564633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 1, 4].length) (baseStart_4564633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564633 prefixEnd_4564633 := by exact prefixLift 4564633
  have htrace : WordTrace (prefixWord ++ tailWord_4564633) baseStart_4564633 baseEnd_4564633 := by
    simpa [prefixWord, tailWord_4564633, baseEnd_4564633] using wordTrace_append hprefix tailTrace_4564633
  have hstable : (prefixWord ++ tailWord_4564633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564633).length < 2 ^ (prefixWord ++ tailWord_4564633).sum := by decide
  have hdescent : baseEnd_4564633 < baseStart_4564633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564663 : List Nat := [1, 1, 3, 1, 5, 1, 4, 1, 6]
def baseStart_4564663 : Nat := 118140960795 + 4564663 * 2 ^ 59
def prefixEnd_4564663 : Nat := 4983230072969 + 3 ^ 40 * 4564663 * 2
def baseEnd_4564663 : Nat := 260429571643797718746667

theorem tailTrace_4564663 : CollatzResearch.WordTrace tailWord_4564663 prefixEnd_4564663 260429571643797718746667 := by
  unfold tailWord_4564663
  simp only [CollatzResearch.WordTrace]
  refine ⟨166486937062013008219786643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110991291374675338813191095 166486937062013008219786643)
  ·
    refine ⟨249730405593019512329679965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166486937062013008219786643 249730405593019512329679965)
    ·
      refine ⟨93648902097382317123629987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249730405593019512329679965 93648902097382317123629987)
      ·
        refine ⟨140473353146073475685444981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93648902097382317123629987 140473353146073475685444981)
        ·
          refine ⟨13169376857444388345510467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140473353146073475685444981 13169376857444388345510467)
          ·
            refine ⟨19754065286166582518265701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13169376857444388345510467 19754065286166582518265701)
            ·
              refine ⟨3703887241156234222174819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19754065286166582518265701 3703887241156234222174819)
              ·
                refine ⟨5555830861734351333262229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3703887241156234222174819 5555830861734351333262229)
                ·
                  refine ⟨260429571643797718746667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5555830861734351333262229 260429571643797718746667)
                  ·
                    rfl

theorem cell23_4564663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 6].length) (baseStart_4564663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564663 prefixEnd_4564663 := by exact prefixLift 4564663
  have htrace : WordTrace (prefixWord ++ tailWord_4564663) baseStart_4564663 baseEnd_4564663 := by
    simpa [prefixWord, tailWord_4564663, baseEnd_4564663] using wordTrace_append hprefix tailTrace_4564663
  have hstable : (prefixWord ++ tailWord_4564663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564663).length < 2 ^ (prefixWord ++ tailWord_4564663).sum := by decide
  have hdescent : baseEnd_4564663 < baseStart_4564663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564674 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_4564674 : Nat := 118140960795 + 4564674 * 2 ^ 59
def prefixEnd_4564674 : Nat := 4983230072969 + 3 ^ 40 * 4564674 * 2
def baseEnd_4564674 : Nat := 2343871793081378925682453

theorem tailTrace_4564674 : CollatzResearch.WordTrace tailWord_4564674 prefixEnd_4564674 2343871793081378925682453 := by
  unfold tailWord_4564674
  simp only [CollatzResearch.WordTrace]
  refine ⟨41621834566243289274609269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110991558843315438065624717 41621834566243289274609269)
  ·
    refine ⟨3902046990585308369494619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41621834566243289274609269 3902046990585308369494619)
    ·
      refine ⟨5853070485877962554241929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3902046990585308369494619 5853070485877962554241929)
      ·
        refine ⟨4389802864408471915681447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5853070485877962554241929 4389802864408471915681447)
        ·
          refine ⟨6584704296612707873522171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4389802864408471915681447 6584704296612707873522171)
          ·
            refine ⟨9877056444919061810283257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6584704296612707873522171 9877056444919061810283257)
            ·
              refine ⟨7407792333689296357712443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9877056444919061810283257 7407792333689296357712443)
              ·
                refine ⟨11111688500533944536568665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7407792333689296357712443 11111688500533944536568665)
                ·
                  refine ⟨8333766375400458402426499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11111688500533944536568665 8333766375400458402426499)
                  ·
                    refine ⟨12500649563100687603639749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8333766375400458402426499 12500649563100687603639749)
                    ·
                      refine ⟨2343871793081378925682453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12500649563100687603639749 2343871793081378925682453)
                      ·
                        rfl

theorem cell23_4564674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_4564674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564674 prefixEnd_4564674 := by exact prefixLift 4564674
  have htrace : WordTrace (prefixWord ++ tailWord_4564674) baseStart_4564674 baseEnd_4564674 := by
    simpa [prefixWord, tailWord_4564674, baseEnd_4564674] using wordTrace_append hprefix tailTrace_4564674
  have hstable : (prefixWord ++ tailWord_4564674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564674).length < 2 ^ (prefixWord ++ tailWord_4564674).sum := by decide
  have hdescent : baseEnd_4564674 < baseStart_4564674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564701 : List Nat := [1, 4, 3, 3, 1, 2, 2, 2, 1, 4]
def baseStart_4564701 : Nat := 118140960795 + 4564701 * 2 ^ 59
def prefixEnd_4564701 : Nat := 4983230072969 + 3 ^ 40 * 4564701 * 2
def baseEnd_4564701 : Nat := 781295219019683440014943

theorem tailTrace_4564701 : CollatzResearch.WordTrace tailWord_4564701 prefixEnd_4564701 781295219019683440014943 := by
  unfold tailWord_4564701
  simp only [CollatzResearch.WordTrace]
  refine ⟨166488323035875340709669957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110992215357250227139779971 166488323035875340709669957)
  ·
    refine ⟨31216560569226626383063117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166488323035875340709669957 31216560569226626383063117)
    ·
      refine ⟨11706210213459984893648669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31216560569226626383063117 11706210213459984893648669)
      ·
        refine ⟨4389828830047494335118251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11706210213459984893648669 4389828830047494335118251)
        ·
          refine ⟨6584743245071241502677377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4389828830047494335118251 6584743245071241502677377)
          ·
            refine ⟨4938557433803431127008033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6584743245071241502677377 4938557433803431127008033)
            ·
              refine ⟨3703918075352573345256025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4938557433803431127008033 3703918075352573345256025)
              ·
                refine ⟨2777938556514430008942019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3703918075352573345256025 2777938556514430008942019)
                ·
                  refine ⟨4166907834771645013413029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2777938556514430008942019 4166907834771645013413029)
                  ·
                    refine ⟨781295219019683440014943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4166907834771645013413029 781295219019683440014943)
                    ·
                      rfl

theorem cell23_4564701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_4564701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564701 prefixEnd_4564701 := by exact prefixLift 4564701
  have htrace : WordTrace (prefixWord ++ tailWord_4564701) baseStart_4564701 baseEnd_4564701 := by
    simpa [prefixWord, tailWord_4564701, baseEnd_4564701] using wordTrace_append hprefix tailTrace_4564701
  have hstable : (prefixWord ++ tailWord_4564701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564701).length < 2 ^ (prefixWord ++ tailWord_4564701).sum := by decide
  have hdescent : baseEnd_4564701 < baseStart_4564701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564716 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 5]
def baseStart_4564716 : Nat := 118140960795 + 4564716 * 2 ^ 59
def prefixEnd_4564716 : Nat := 4983230072969 + 3 ^ 40 * 4564716 * 2
def baseEnd_4564716 : Nat := 2343893359268867761357259

theorem tailTrace_4564716 : CollatzResearch.WordTrace tailWord_4564716 prefixEnd_4564716 2343893359268867761357259 := by
  unfold tailWord_4564716
  simp only [CollatzResearch.WordTrace]
  refine ⟨83244435065410499135733001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110992580087213998847644001 83244435065410499135733001)
  ·
    refine ⟨62433326299057874351799751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83244435065410499135733001 62433326299057874351799751)
    ·
      refine ⟨93649989448586811527699627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62433326299057874351799751 93649989448586811527699627)
      ·
        refine ⟨140474984172880217291549441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93649989448586811527699627 140474984172880217291549441)
        ·
          refine ⟨105356238129660162968662081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140474984172880217291549441 105356238129660162968662081)
          ·
            refine ⟨79017178597245122226496561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105356238129660162968662081 79017178597245122226496561)
            ·
              refine ⟨59262883947933841669872421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79017178597245122226496561 59262883947933841669872421)
              ·
                refine ⟨11111790740237595313101079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59262883947933841669872421 11111790740237595313101079)
                ·
                  refine ⟨16667686110356392969651619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11111790740237595313101079 16667686110356392969651619)
                  ·
                    refine ⟨25001529165534589454477429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16667686110356392969651619 25001529165534589454477429)
                    ·
                      refine ⟨2343893359268867761357259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25001529165534589454477429 2343893359268867761357259)
                      ·
                        rfl

theorem cell23_4564716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_4564716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564716 prefixEnd_4564716 := by exact prefixLift 4564716
  have htrace : WordTrace (prefixWord ++ tailWord_4564716) baseStart_4564716 baseEnd_4564716 := by
    simpa [prefixWord, tailWord_4564716, baseEnd_4564716] using wordTrace_append hprefix tailTrace_4564716
  have hstable : (prefixWord ++ tailWord_4564716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564716).length < 2 ^ (prefixWord ++ tailWord_4564716).sum := by decide
  have hdescent : baseEnd_4564716 < baseStart_4564716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564723 : List Nat := [1, 1, 1, 2, 2, 3, 4, 3, 2, 4]
def baseStart_4564723 : Nat := 118140960795 + 4564723 * 2 ^ 59
def prefixEnd_4564723 : Nat := 4983230072969 + 3 ^ 40 * 4564723 * 2
def baseEnd_4564723 : Nat := 781298984544483077989909

theorem tailTrace_4564723 : CollatzResearch.WordTrace tailWord_4564723 prefixEnd_4564723 781298984544483077989909 := by
  unfold tailWord_4564723
  simp only [CollatzResearch.WordTrace]
  refine ⟨166489125441795638466970823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110992750294530425644647215 166489125441795638466970823)
  ·
    refine ⟨249733688162693457700456235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166489125441795638466970823 249733688162693457700456235)
    ·
      refine ⟨374600532244040186550684353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249733688162693457700456235 374600532244040186550684353)
      ·
        refine ⟨280950399183030139913013265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374600532244040186550684353 280950399183030139913013265)
        ·
          refine ⟨210712799387272604934759949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280950399183030139913013265 210712799387272604934759949)
          ·
            refine ⟨79017299770227226850534981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210712799387272604934759949 79017299770227226850534981)
            ·
              refine ⟨14815743706917605034475309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79017299770227226850534981 14815743706917605034475309)
              ·
                refine ⟨5555903890094101887928241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14815743706917605034475309 5555903890094101887928241)
                ·
                  refine ⟨4166927917570576415946181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5555903890094101887928241 4166927917570576415946181)
                  ·
                    refine ⟨781298984544483077989909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4166927917570576415946181 781298984544483077989909)
                    ·
                      rfl

theorem cell23_4564723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 4].length) (baseStart_4564723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564723 prefixEnd_4564723 := by exact prefixLift 4564723
  have htrace : WordTrace (prefixWord ++ tailWord_4564723) baseStart_4564723 baseEnd_4564723 := by
    simpa [prefixWord, tailWord_4564723, baseEnd_4564723] using wordTrace_append hprefix tailTrace_4564723
  have hstable : (prefixWord ++ tailWord_4564723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564723).length < 2 ^ (prefixWord ++ tailWord_4564723).sum := by decide
  have hdescent : baseEnd_4564723 < baseStart_4564723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564724 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_4564724 : Nat := 118140960795 + 4564724 * 2 ^ 59
def prefixEnd_4564724 : Nat := 4983230072969 + 3 ^ 40 * 4564724 * 2
def baseEnd_4564724 : Nat := 2343897467114103730057223

theorem tailTrace_4564724 : CollatzResearch.WordTrace tailWord_4564724 prefixEnd_4564724 2343897467114103730057223 := by
  unfold tailWord_4564724
  simp only [CollatzResearch.WordTrace]
  refine ⟨83244580957396007818878613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110992774609861343758504817 83244580957396007818878613)
  ·
    refine ⟨3902089732377937866509935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83244580957396007818878613 3902089732377937866509935)
    ·
      refine ⟨5853134598566906799764903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3902089732377937866509935 5853134598566906799764903)
      ·
        refine ⟨8779701897850360199647355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5853134598566906799764903 8779701897850360199647355)
        ·
          refine ⟨13169552846775540299471033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8779701897850360199647355 13169552846775540299471033)
          ·
            refine ⟨9877164635081655224603275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13169552846775540299471033 9877164635081655224603275)
            ·
              refine ⟨14815746952622482836904913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9877164635081655224603275 14815746952622482836904913)
              ·
                refine ⟨11111810214466862127678685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14815746952622482836904913 11111810214466862127678685)
                ·
                  refine ⟨4166928830425073297879507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11111810214466862127678685 4166928830425073297879507)
                  ·
                    refine ⟨6250393245637609946819261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4166928830425073297879507 6250393245637609946819261)
                    ·
                      refine ⟨2343897467114103730057223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6250393245637609946819261 2343897467114103730057223)
                      ·
                        rfl

theorem cell23_4564724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_4564724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564724 prefixEnd_4564724 := by exact prefixLift 4564724
  have htrace : WordTrace (prefixWord ++ tailWord_4564724) baseStart_4564724 baseEnd_4564724 := by
    simpa [prefixWord, tailWord_4564724, baseEnd_4564724] using wordTrace_append hprefix tailTrace_4564724
  have hstable : (prefixWord ++ tailWord_4564724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564724).length < 2 ^ (prefixWord ++ tailWord_4564724).sum := by decide
  have hdescent : baseEnd_4564724 < baseStart_4564724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564734 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_4564734 : Nat := 118140960795 + 4564734 * 2 ^ 59
def prefixEnd_4564734 : Nat := 4983230072969 + 3 ^ 40 * 4564734 * 2
def baseEnd_4564734 : Nat := 2343902601920648690932177

theorem tailTrace_4564734 : CollatzResearch.WordTrace tailWord_4564734 prefixEnd_4564734 2343902601920648690932177 := by
  unfold tailWord_4564734
  simp only [CollatzResearch.WordTrace]
  refine ⟨20811190830594473418202657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110993017763170524897080837 20811190830594473418202657)
  ·
    refine ⟨15608393122945855063651993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20811190830594473418202657 15608393122945855063651993)
    ·
      refine ⟨11706294842209391297738995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15608393122945855063651993 11706294842209391297738995)
      ·
        refine ⟨17559442263314086946608493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11706294842209391297738995 17559442263314086946608493)
        ·
          refine ⟨6584790848742782604978185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17559442263314086946608493 6584790848742782604978185)
          ·
            refine ⟨4938593136557086953733639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6584790848742782604978185 4938593136557086953733639)
            ·
              refine ⟨7407889704835630430600459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4938593136557086953733639 7407889704835630430600459)
              ·
                refine ⟨11111834557253445645900689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7407889704835630430600459 11111834557253445645900689)
                ·
                  refine ⟨8333875917940084234425517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11111834557253445645900689 8333875917940084234425517)
                  ·
                    refine ⟨3125203469227531587909569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8333875917940084234425517 3125203469227531587909569)
                    ·
                      refine ⟨2343902601920648690932177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3125203469227531587909569 2343902601920648690932177)
                      ·
                        rfl

theorem cell23_4564734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_4564734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564734 prefixEnd_4564734 := by exact prefixLift 4564734
  have htrace : WordTrace (prefixWord ++ tailWord_4564734) baseStart_4564734 baseEnd_4564734 := by
    simpa [prefixWord, tailWord_4564734, baseEnd_4564734] using wordTrace_append hprefix tailTrace_4564734
  have hstable : (prefixWord ++ tailWord_4564734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564734).length < 2 ^ (prefixWord ++ tailWord_4564734).sum := by decide
  have hdescent : baseEnd_4564734 < baseStart_4564734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564747 : List Nat := [1, 1, 1, 1, 5, 1, 3, 5, 1, 2, 2]
def baseStart_4564747 : Nat := 118140960795 + 4564747 * 2 ^ 59
def prefixEnd_4564747 : Nat := 4983230072969 + 3 ^ 40 * 4564747 * 2
def baseEnd_4564747 : Nat := 2343909277169157140069617

theorem tailTrace_4564747 : CollatzResearch.WordTrace tailWord_4564747 prefixEnd_4564747 2343909277169157140069617 := by
  unfold tailWord_4564747
  simp only [CollatzResearch.WordTrace]
  refine ⟨166490000793708690565844495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110993333862472460377229663 166490000793708690565844495)
  ·
    refine ⟨249735001190563035848766743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166490000793708690565844495 249735001190563035848766743)
    ·
      refine ⟨374602501785844553773150115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249735001190563035848766743 374602501785844553773150115)
      ·
        refine ⟨561903752678766830659725173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374602501785844553773150115 561903752678766830659725173)
        ·
          refine ⟨52678476813634390374349235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 561903752678766830659725173 52678476813634390374349235)
          ·
            refine ⟨79017715220451585561523853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52678476813634390374349235 79017715220451585561523853)
            ·
              refine ⟨29631643207669344585571445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79017715220451585561523853 29631643207669344585571445)
              ·
                refine ⟨2777966550719001054897323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29631643207669344585571445 2777966550719001054897323)
                ·
                  refine ⟨4166949826078501582345985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2777966550719001054897323 4166949826078501582345985)
                  ·
                    refine ⟨3125212369558876186759489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4166949826078501582345985 3125212369558876186759489)
                    ·
                      refine ⟨2343909277169157140069617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3125212369558876186759489 2343909277169157140069617)
                      ·
                        rfl

theorem cell23_4564747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 1, 2, 2].length) (baseStart_4564747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564747 prefixEnd_4564747 := by exact prefixLift 4564747
  have htrace : WordTrace (prefixWord ++ tailWord_4564747) baseStart_4564747 baseEnd_4564747 := by
    simpa [prefixWord, tailWord_4564747, baseEnd_4564747] using wordTrace_append hprefix tailTrace_4564747
  have hstable : (prefixWord ++ tailWord_4564747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564747).length < 2 ^ (prefixWord ++ tailWord_4564747).sum := by decide
  have hdescent : baseEnd_4564747 < baseStart_4564747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564763 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 4, 1, 3]
def baseStart_4564763 : Nat := 118140960795 + 4564763 * 2 ^ 59
def prefixEnd_4564763 : Nat := 4983230072969 + 3 ^ 40 * 4564763 * 2
def baseEnd_4564763 : Nat := 2343917492859629077469543

theorem tailTrace_4564763 : CollatzResearch.WordTrace tailWord_4564763 prefixEnd_4564763 2343917492859629077469543 := by
  unfold tailWord_4564763
  simp only [CollatzResearch.WordTrace]
  refine ⟨166490584361650725298426943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110993722907767150198951295 166490584361650725298426943)
  ·
    refine ⟨249735876542476087947640415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166490584361650725298426943 249735876542476087947640415)
    ·
      refine ⟨374603814813714131921460623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249735876542476087947640415 374603814813714131921460623)
      ·
        refine ⟨561905722220571197882190935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374603814813714131921460623 561905722220571197882190935)
        ·
          refine ⟨842858583330856796823286403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561905722220571197882190935 842858583330856796823286403)
          ·
            refine ⟨1264287874996285195234929605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842858583330856796823286403 1264287874996285195234929605)
            ·
              refine ⟨237053976561803474106549301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1264287874996285195234929605 237053976561803474106549301)
              ·
                refine ⟨22223810302669075697488997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 237053976561803474106549301 22223810302669075697488997)
                ·
                  refine ⟨4166964431750451693279187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22223810302669075697488997 4166964431750451693279187)
                  ·
                    refine ⟨6250446647625677539918781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4166964431750451693279187 6250446647625677539918781)
                    ·
                      refine ⟨2343917492859629077469543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6250446647625677539918781 2343917492859629077469543)
                      ·
                        rfl

theorem cell23_4564763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 1, 3].length) (baseStart_4564763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564763 prefixEnd_4564763 := by exact prefixLift 4564763
  have htrace : WordTrace (prefixWord ++ tailWord_4564763) baseStart_4564763 baseEnd_4564763 := by
    simpa [prefixWord, tailWord_4564763, baseEnd_4564763] using wordTrace_append hprefix tailTrace_4564763
  have hstable : (prefixWord ++ tailWord_4564763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564763).length < 2 ^ (prefixWord ++ tailWord_4564763).sum := by decide
  have hdescent : baseEnd_4564763 < baseStart_4564763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564780 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 3]
def baseStart_4564780 : Nat := 118140960795 + 4564780 * 2 ^ 59
def prefixEnd_4564780 : Nat := 4983230072969 + 3 ^ 40 * 4564780 * 2
def baseEnd_4564780 : Nat := 2343926222030755510956965

theorem tailTrace_4564780 : CollatzResearch.WordTrace tailWord_4564780 prefixEnd_4564780 2343926222030755510956965 := by
  unfold tailWord_4564780
  simp only [CollatzResearch.WordTrace]
  refine ⟨83245602201294568600897897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110994136268392758134530529 83245602201294568600897897)
  ·
    refine ⟨62434201650970926450673423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83245602201294568600897897 62434201650970926450673423)
    ·
      refine ⟨93651302476456389676010135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62434201650970926450673423 93651302476456389676010135)
      ·
        refine ⟨140476953714684584514015203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93651302476456389676010135 140476953714684584514015203)
        ·
          refine ⟨210715430572026876771022805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140476953714684584514015203 210715430572026876771022805)
          ·
            refine ⟨4938642904031879924320847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 210715430572026876771022805 4938642904031879924320847)
            ·
              refine ⟨7407964356047819886481271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4938642904031879924320847 7407964356047819886481271)
              ·
                refine ⟨11111946534071729829721907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7407964356047819886481271 11111946534071729829721907)
                ·
                  refine ⟨16667919801107594744582861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11111946534071729829721907 16667919801107594744582861)
                  ·
                    refine ⟨6250469925415348029218573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16667919801107594744582861 6250469925415348029218573)
                    ·
                      refine ⟨2343926222030755510956965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6250469925415348029218573 2343926222030755510956965)
                      ·
                        rfl

theorem cell23_4564780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_4564780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564780 prefixEnd_4564780 := by exact prefixLift 4564780
  have htrace : WordTrace (prefixWord ++ tailWord_4564780) baseStart_4564780 baseEnd_4564780 := by
    simpa [prefixWord, tailWord_4564780, baseEnd_4564780] using wordTrace_append hprefix tailTrace_4564780
  have hstable : (prefixWord ++ tailWord_4564780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564780).length < 2 ^ (prefixWord ++ tailWord_4564780).sum := by decide
  have hdescent : baseEnd_4564780 < baseStart_4564780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564796 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 1, 8]
def baseStart_4564796 : Nat := 118140960795 + 4564796 * 2 ^ 59
def prefixEnd_4564796 : Nat := 4983230072969 + 3 ^ 40 * 4564796 * 2
def baseEnd_4564796 : Nat := 781311479240409149452297

theorem tailTrace_4564796 : CollatzResearch.WordTrace tailWord_4564796 prefixEnd_4564796 781311479240409149452297 := by
  unfold tailWord_4564796
  simp only [CollatzResearch.WordTrace]
  refine ⟨83245893985265585967189121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110994525313687447956252161 83245893985265585967189121)
  ·
    refine ⟨62434420488949189475391841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83245893985265585967189121 62434420488949189475391841)
    ·
      refine ⟨46825815366711892106543881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62434420488949189475391841 46825815366711892106543881)
      ·
        refine ⟨35119361525033919079907911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46825815366711892106543881 35119361525033919079907911)
        ·
          refine ⟨52679042287550878619861867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35119361525033919079907911 52679042287550878619861867)
          ·
            refine ⟨79018563431326317929792801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52679042287550878619861867 79018563431326317929792801)
            ·
              refine ⟨59263922573494738447344601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79018563431326317929792801 59263922573494738447344601)
              ·
                refine ⟨44447941930121053835508451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59263922573494738447344601 44447941930121053835508451)
                ·
                  refine ⟨66671912895181580753262677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44447941930121053835508451 66671912895181580753262677)
                  ·
                    refine ⟨781311479240409149452297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66671912895181580753262677 781311479240409149452297)
                    ·
                      rfl

theorem cell23_4564796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_4564796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564796 prefixEnd_4564796 := by exact prefixLift 4564796
  have htrace : WordTrace (prefixWord ++ tailWord_4564796) baseStart_4564796 baseEnd_4564796 := by
    simpa [prefixWord, tailWord_4564796, baseEnd_4564796] using wordTrace_append hprefix tailTrace_4564796
  have hstable : (prefixWord ++ tailWord_4564796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564796).length < 2 ^ (prefixWord ++ tailWord_4564796).sum := by decide
  have hdescent : baseEnd_4564796 < baseStart_4564796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564854 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2]
def baseStart_4564854 : Nat := 118140960795 + 4564854 * 2 ^ 59
def prefixEnd_4564854 : Nat := 4983230072969 + 3 ^ 40 * 4564854 * 2
def baseEnd_4564854 : Nat := 2343964219599188221431625

theorem tailTrace_4564854 : CollatzResearch.WordTrace tailWord_4564854 prefixEnd_4564854 2343964219599188221431625 := by
  unfold tailWord_4564854
  simp only [CollatzResearch.WordTrace]
  refine ⟨10405868962770065489999351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110995935602880698559993077 10405868962770065489999351)
  ·
    refine ⟨15608803444155098234999027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10405868962770065489999351 15608803444155098234999027)
    ·
      refine ⟨23413205166232647352498541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15608803444155098234999027 23413205166232647352498541)
      ·
        refine ⟨8779951937337242757186953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23413205166232647352498541 8779951937337242757186953)
        ·
          refine ⟨6584963953002932067890215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8779951937337242757186953 6584963953002932067890215)
          ·
            refine ⟨9877445929504398101835323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6584963953002932067890215 9877445929504398101835323)
            ·
              refine ⟨14816168894256597152752985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9877445929504398101835323 14816168894256597152752985)
              ·
                refine ⟨11112126670692447864564739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14816168894256597152752985 11112126670692447864564739)
                ·
                  refine ⟨16668190006038671796847109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11112126670692447864564739 16668190006038671796847109)
                  ·
                    refine ⟨3125285626132250961908833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16668190006038671796847109 3125285626132250961908833)
                    ·
                      refine ⟨2343964219599188221431625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3125285626132250961908833 2343964219599188221431625)
                      ·
                        rfl

theorem cell23_4564854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_4564854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564854 prefixEnd_4564854 := by exact prefixLift 4564854
  have htrace : WordTrace (prefixWord ++ tailWord_4564854) baseStart_4564854 baseEnd_4564854 := by
    simpa [prefixWord, tailWord_4564854, baseEnd_4564854] using wordTrace_append hprefix tailTrace_4564854
  have hstable : (prefixWord ++ tailWord_4564854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564854).length < 2 ^ (prefixWord ++ tailWord_4564854).sum := by decide
  have hdescent : baseEnd_4564854 < baseStart_4564854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564856 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 5, 7]
def baseStart_4564856 : Nat := 118140960795 + 4564856 * 2 ^ 59
def prefixEnd_4564856 : Nat := 4983230072969 + 3 ^ 40 * 4564856 * 2
def baseEnd_4564856 : Nat := 781321748853499071202205

theorem tailTrace_4564856 : CollatzResearch.WordTrace tailWord_4564856 prefixEnd_4564856 781321748853499071202205 := by
  unfold tailWord_4564856
  simp only [CollatzResearch.WordTrace]
  refine ⟨83246988175156901090781211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110995984233542534787708281 83246988175156901090781211)
  ·
    refine ⟨124870482262735351636171817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83246988175156901090781211 124870482262735351636171817)
    ·
      refine ⟨93652861697051513727128863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124870482262735351636171817 93652861697051513727128863)
      ·
        refine ⟨140479292545577270590693295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93652861697051513727128863 140479292545577270590693295)
        ·
          refine ⟨210718938818365905886039943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140479292545577270590693295 210718938818365905886039943)
          ·
            refine ⟨316078408227548858829059915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210718938818365905886039943 316078408227548858829059915)
            ·
              refine ⟨474117612341323288243589873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316078408227548858829059915 474117612341323288243589873)
              ·
                refine ⟨355588209255992466182692405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474117612341323288243589873 355588209255992466182692405)
                ·
                  refine ⟨33336394617749293704627413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 355588209255992466182692405 33336394617749293704627413)
                  ·
                    refine ⟨781321748853499071202205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33336394617749293704627413 781321748853499071202205)
                    ·
                      rfl

theorem cell23_4564856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_4564856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564856 prefixEnd_4564856 := by exact prefixLift 4564856
  have htrace : WordTrace (prefixWord ++ tailWord_4564856) baseStart_4564856 baseEnd_4564856 := by
    simpa [prefixWord, tailWord_4564856, baseEnd_4564856] using wordTrace_append hprefix tailTrace_4564856
  have hstable : (prefixWord ++ tailWord_4564856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564856).length < 2 ^ (prefixWord ++ tailWord_4564856).sum := by decide
  have hdescent : baseEnd_4564856 < baseStart_4564856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564873 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 2, 5]
def baseStart_4564873 : Nat := 118140960795 + 4564873 * 2 ^ 59
def prefixEnd_4564873 : Nat := 4983230072969 + 3 ^ 40 * 4564873 * 2
def baseEnd_4564873 : Nat := 781324658577207882364679

theorem tailTrace_4564873 : CollatzResearch.WordTrace tailWord_4564873 prefixEnd_4564873 781324658577207882364679 := by
  unfold tailWord_4564873
  simp only [CollatzResearch.WordTrace]
  refine ⟨166494596391252214084931273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110996397594168142723287515 166494596391252214084931273)
  ·
    refine ⟨124870947293439160563698455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166494596391252214084931273 124870947293439160563698455)
    ·
      refine ⟨187306420940158740845547683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124870947293439160563698455 187306420940158740845547683)
      ·
        refine ⟨280959631410238111268321525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187306420940158740845547683 280959631410238111268321525)
        ·
          refine ⟨26339965444709822931405143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 280959631410238111268321525 26339965444709822931405143)
          ·
            refine ⟨39509948167064734397107715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26339965444709822931405143 39509948167064734397107715)
            ·
              refine ⟨59264922250597101595661573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39509948167064734397107715 59264922250597101595661573)
              ·
                refine ⟨11112172921986956549186545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59264922250597101595661573 11112172921986956549186545)
                ·
                  refine ⟨8334129691490217411889909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11112172921986956549186545 8334129691490217411889909)
                  ·
                    refine ⟨781324658577207882364679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8334129691490217411889909 781324658577207882364679)
                    ·
                      rfl

theorem cell23_4564873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 5].length) (baseStart_4564873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564873 prefixEnd_4564873 := by exact prefixLift 4564873
  have htrace : WordTrace (prefixWord ++ tailWord_4564873) baseStart_4564873 baseEnd_4564873 := by
    simpa [prefixWord, tailWord_4564873, baseEnd_4564873] using wordTrace_append hprefix tailTrace_4564873
  have hstable : (prefixWord ++ tailWord_4564873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564873).length < 2 ^ (prefixWord ++ tailWord_4564873).sum := by decide
  have hdescent : baseEnd_4564873 < baseStart_4564873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4564933 : List Nat := [1, 3, 1, 1, 1, 1, 1, 8, 6]
def baseStart_4564933 : Nat := 118140960795 + 4564933 * 2 ^ 59
def prefixEnd_4564933 : Nat := 4983230072969 + 3 ^ 40 * 4564933 * 2
def baseEnd_4564933 : Nat := 260444976063432601371529

theorem tailTrace_4564933 : CollatzResearch.WordTrace tailWord_4564933 prefixEnd_4564933 260444976063432601371529 := by
  unfold tailWord_4564933
  simp only [CollatzResearch.WordTrace]
  refine ⟨166496784771034844332115453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110997856514023229554743635 166496784771034844332115453)
  ·
    refine ⟨62436294289138066624543295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166496784771034844332115453 62436294289138066624543295)
    ·
      refine ⟨93654441433707099936814943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62436294289138066624543295 93654441433707099936814943)
      ·
        refine ⟨140481662150560649905222415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93654441433707099936814943 140481662150560649905222415)
        ·
          refine ⟨210722493225840974857833623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140481662150560649905222415 210722493225840974857833623)
          ·
            refine ⟨316083739838761462286750435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210722493225840974857833623 316083739838761462286750435)
            ·
              refine ⟨474125609758142193430125653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316083739838761462286750435 474125609758142193430125653)
              ·
                refine ⟨5556159489353228829259285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 474125609758142193430125653 5556159489353228829259285)
                ·
                  refine ⟨260444976063432601371529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5556159489353228829259285 260444976063432601371529)
                  ·
                    rfl

theorem cell23_4564933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 6].length) (baseStart_4564933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4564933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4564933 prefixEnd_4564933 := by exact prefixLift 4564933
  have htrace : WordTrace (prefixWord ++ tailWord_4564933) baseStart_4564933 baseEnd_4564933 := by
    simpa [prefixWord, tailWord_4564933, baseEnd_4564933] using wordTrace_append hprefix tailTrace_4564933
  have hstable : (prefixWord ++ tailWord_4564933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4564933).length < 2 ^ (prefixWord ++ tailWord_4564933).sum := by decide
  have hdescent : baseEnd_4564933 < baseStart_4564933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4564933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565000 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_4565000 : Nat := 118140960795 + 4565000 * 2 ^ 59
def prefixEnd_4565000 : Nat := 4983230072969 + 3 ^ 40 * 4565000 * 2
def baseEnd_4565000 : Nat := 2344039187774744650205953

theorem tailTrace_4565000 : CollatzResearch.WordTrace tailWord_4565000 prefixEnd_4565000 2344039187774744650205953 := by
  unfold tailWord_4565000
  simp only [CollatzResearch.WordTrace]
  refine ⟨83249614230896057387402227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110999485641194743183202969 83249614230896057387402227)
  ·
    refine ⟨124874421346344086081103341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83249614230896057387402227 124874421346344086081103341)
    ·
      refine ⟨46827908004879032280413753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124874421346344086081103341 46827908004879032280413753)
      ·
        refine ⟨35120931003659274210310315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46827908004879032280413753 35120931003659274210310315)
        ·
          refine ⟨52681396505488911315465473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35120931003659274210310315 52681396505488911315465473)
          ·
            refine ⟨39511047379116683486599105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52681396505488911315465473 39511047379116683486599105)
            ·
              refine ⟨29633285534337512614949329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39511047379116683486599105 29633285534337512614949329)
              ·
                refine ⟨22224964150753134461211997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29633285534337512614949329 22224964150753134461211997)
                ·
                  refine ⟨8334361556532425422954499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22224964150753134461211997 8334361556532425422954499)
                  ·
                    refine ⟨12501542334798638134431749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8334361556532425422954499 12501542334798638134431749)
                    ·
                      refine ⟨2344039187774744650205953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12501542334798638134431749 2344039187774744650205953)
                      ·
                        rfl

theorem cell23_4565000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_4565000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565000 prefixEnd_4565000 := by exact prefixLift 4565000
  have htrace : WordTrace (prefixWord ++ tailWord_4565000) baseStart_4565000 baseEnd_4565000 := by
    simpa [prefixWord, tailWord_4565000, baseEnd_4565000] using wordTrace_append hprefix tailTrace_4565000
  have hstable : (prefixWord ++ tailWord_4565000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565000).length < 2 ^ (prefixWord ++ tailWord_4565000).sum := by decide
  have hdescent : baseEnd_4565000 < baseStart_4565000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565017 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 5, 2, 2]
def baseStart_4565017 : Nat := 118140960795 + 4565017 * 2 ^ 59
def prefixEnd_4565017 : Nat := 4983230072969 + 3 ^ 40 * 4565017 * 2
def baseEnd_4565017 : Nat := 2344047916945871083693375

theorem tailTrace_4565017 : CollatzResearch.WordTrace tailWord_4565017 prefixEnd_4565017 2344047916945871083693375 := by
  unfold tailWord_4565017
  simp only [CollatzResearch.WordTrace]
  refine ⟨166499848502730526678173305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110999899001820351118782203 166499848502730526678173305)
  ·
    refine ⟨124874886377047895008629979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166499848502730526678173305 124874886377047895008629979)
    ·
      refine ⟨187312329565571842512944969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124874886377047895008629979 187312329565571842512944969)
      ·
        refine ⟨140484247174178881884708727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187312329565571842512944969 140484247174178881884708727)
        ·
          refine ⟨210726370761268322827063091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140484247174178881884708727 210726370761268322827063091)
          ·
            refine ⟨316089556141902484240594637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210726370761268322827063091 316089556141902484240594637)
            ·
              refine ⟨118533583553213431590222989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 316089556141902484240594637 118533583553213431590222989)
              ·
                refine ⟨44450093832455036846333621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118533583553213431590222989 44450093832455036846333621)
                ·
                  refine ⟨4167196296792659704343777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44450093832455036846333621 4167196296792659704343777)
                  ·
                    refine ⟨3125397222594494778257833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4167196296792659704343777 3125397222594494778257833)
                    ·
                      refine ⟨2344047916945871083693375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3125397222594494778257833 2344047916945871083693375)
                      ·
                        rfl

theorem cell23_4565017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 2, 2].length) (baseStart_4565017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565017 prefixEnd_4565017 := by exact prefixLift 4565017
  have htrace : WordTrace (prefixWord ++ tailWord_4565017) baseStart_4565017 baseEnd_4565017 := by
    simpa [prefixWord, tailWord_4565017, baseEnd_4565017] using wordTrace_append hprefix tailTrace_4565017
  have hstable : (prefixWord ++ tailWord_4565017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565017).length < 2 ^ (prefixWord ++ tailWord_4565017).sum := by decide
  have hdescent : baseEnd_4565017 < baseStart_4565017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565023 : List Nat := [1, 1, 2, 4, 1, 2, 1, 11]
def baseStart_4565023 : Nat := 118140960795 + 4565023 * 2 ^ 59
def prefixEnd_4565023 : Nat := 4983230072969 + 3 ^ 40 * 4565023 * 2
def baseEnd_4565023 : Nat := 86816703623325854082161

theorem tailTrace_4565023 : CollatzResearch.WordTrace tailWord_4565023 prefixEnd_4565023 86816703623325854082161 := by
  unfold tailWord_4565023
  simp only [CollatzResearch.WordTrace]
  refine ⟨166500067340708789702891723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111000044893805859801927815 166500067340708789702891723)
  ·
    refine ⟨249750101011063184554337585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166500067340708789702891723 249750101011063184554337585)
    ·
      refine ⟨187312575758297388415753189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249750101011063184554337585 187312575758297388415753189)
      ·
        refine ⟨35121107954680760327953723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187312575758297388415753189 35121107954680760327953723)
        ·
          refine ⟨52681661932021140491930585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35121107954680760327953723 52681661932021140491930585)
          ·
            refine ⟨39511246449015855368947939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52681661932021140491930585 39511246449015855368947939)
            ·
              refine ⟨59266869673523783053421909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39511246449015855368947939 59266869673523783053421909)
              ·
                refine ⟨86816703623325854082161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 59266869673523783053421909 86816703623325854082161)
                ·
                  rfl

theorem cell23_4565023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 11].length) (baseStart_4565023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565023 prefixEnd_4565023 := by exact prefixLift 4565023
  have htrace : WordTrace (prefixWord ++ tailWord_4565023) baseStart_4565023 baseEnd_4565023 := by
    simpa [prefixWord, tailWord_4565023, baseEnd_4565023] using wordTrace_append hprefix tailTrace_4565023
  have hstable : (prefixWord ++ tailWord_4565023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565023).length < 2 ^ (prefixWord ++ tailWord_4565023).sum := by decide
  have hdescent : baseEnd_4565023 < baseStart_4565023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565031 : List Nat := [1, 1, 7, 1, 2, 1, 3, 1, 1, 5]
def baseStart_4565031 : Nat := 118140960795 + 4565031 * 2 ^ 59
def prefixEnd_4565031 : Nat := 4983230072969 + 3 ^ 40 * 4565031 * 2
def baseEnd_4565031 : Nat := 781351701891678009639437

theorem tailTrace_4565031 : CollatzResearch.WordTrace tailWord_4565031 prefixEnd_4565031 781351701891678009639437 := by
  unfold tailWord_4565031
  simp only [CollatzResearch.WordTrace]
  refine ⟨166500359124679807069182947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111000239416453204712788631 166500359124679807069182947)
  ·
    refine ⟨249750538687019710603774421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166500359124679807069182947 249750538687019710603774421)
    ·
      refine ⟨5853528250477024467275963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 249750538687019710603774421 5853528250477024467275963)
      ·
        refine ⟨8780292375715536700913945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5853528250477024467275963 8780292375715536700913945)
        ·
          refine ⟨6585219281786652525685459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8780292375715536700913945 6585219281786652525685459)
          ·
            refine ⟨9877828922679978788528189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6585219281786652525685459 9877828922679978788528189)
            ·
              refine ⟨3704185846004992045698071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9877828922679978788528189 3704185846004992045698071)
              ·
                refine ⟨5556278769007488068547107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3704185846004992045698071 5556278769007488068547107)
                ·
                  refine ⟨8334418153511232102820661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5556278769007488068547107 8334418153511232102820661)
                  ·
                    refine ⟨781351701891678009639437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8334418153511232102820661 781351701891678009639437)
                    ·
                      rfl

theorem cell23_4565031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_4565031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565031 prefixEnd_4565031 := by exact prefixLift 4565031
  have htrace : WordTrace (prefixWord ++ tailWord_4565031) baseStart_4565031 baseEnd_4565031 := by
    simpa [prefixWord, tailWord_4565031, baseEnd_4565031] using wordTrace_append hprefix tailTrace_4565031
  have hstable : (prefixWord ++ tailWord_4565031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565031).length < 2 ^ (prefixWord ++ tailWord_4565031).sum := by decide
  have hdescent : baseEnd_4565031 < baseStart_4565031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565050 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3]
def baseStart_4565050 : Nat := 118140960795 + 4565050 * 2 ^ 59
def prefixEnd_4565050 : Nat := 4983230072969 + 3 ^ 40 * 4565050 * 2
def baseEnd_4565050 : Nat := 2344064861807469454580723

theorem tailTrace_4565050 : CollatzResearch.WordTrace tailWord_4565050 prefixEnd_4565050 2344064861807469454580723 := by
  unfold tailWord_4565050
  simp only [CollatzResearch.WordTrace]
  refine ⟨41625263027902743328531151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111000701407740648876083069 41625263027902743328531151)
  ·
    refine ⟨62437894541854114992796727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41625263027902743328531151 62437894541854114992796727)
    ·
      refine ⟨93656841812781172489195091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62437894541854114992796727 93656841812781172489195091)
      ·
        refine ⟨140485262719171758733792637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93656841812781172489195091 140485262719171758733792637)
        ·
          refine ⟨52681973519689409525172239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140485262719171758733792637 52681973519689409525172239)
          ·
            refine ⟨79022960279534114287758359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52681973519689409525172239 79022960279534114287758359)
            ·
              refine ⟨118534440419301171431637539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79022960279534114287758359 118534440419301171431637539)
              ·
                refine ⟨177801660628951757147456309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118534440419301171431637539 177801660628951757147456309)
                ·
                  refine ⟨16668905683964227232574029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 177801660628951757147456309 16668905683964227232574029)
                  ·
                    refine ⟨6250839631486585212215261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16668905683964227232574029 6250839631486585212215261)
                    ·
                      refine ⟨2344064861807469454580723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6250839631486585212215261 2344064861807469454580723)
                      ·
                        rfl

theorem cell23_4565050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_4565050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565050 prefixEnd_4565050 := by exact prefixLift 4565050
  have htrace : WordTrace (prefixWord ++ tailWord_4565050) baseStart_4565050 baseEnd_4565050 := by
    simpa [prefixWord, tailWord_4565050, baseEnd_4565050] using wordTrace_append hprefix tailTrace_4565050
  have hstable : (prefixWord ++ tailWord_4565050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565050).length < 2 ^ (prefixWord ++ tailWord_4565050).sum := by decide
  have hdescent : baseEnd_4565050 < baseStart_4565050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565057 : List Nat := [1, 2, 5, 1, 2, 3, 1, 8]
def baseStart_4565057 : Nat := 118140960795 + 4565057 * 2 ^ 59
def prefixEnd_4565057 : Nat := 4983230072969 + 3 ^ 40 * 4565057 * 2
def baseEnd_4565057 : Nat := 86817350228594478784933

theorem tailTrace_4565057 : CollatzResearch.WordTrace tailWord_4565057 prefixEnd_4565057 86817350228594478784933 := by
  unfold tailWord_4565057
  simp only [CollatzResearch.WordTrace]
  refine ⟨166501307422585613509629425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111000871615057075673086283 166501307422585613509629425)
  ·
    refine ⟨124875980566939210132222069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166501307422585613509629425 124875980566939210132222069)
    ·
      refine ⟨11707123178150550949895819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124875980566939210132222069 11707123178150550949895819)
      ·
        refine ⟨17560684767225826424843729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11707123178150550949895819 17560684767225826424843729)
        ·
          refine ⟨13170513575419369818632797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17560684767225826424843729 13170513575419369818632797)
          ·
            refine ⟨4938942590782263681987299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13170513575419369818632797 4938942590782263681987299)
            ·
              refine ⟨7408413886173395522980949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4938942590782263681987299 7408413886173395522980949)
              ·
                refine ⟨86817350228594478784933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7408413886173395522980949 86817350228594478784933)
                ·
                  rfl

theorem cell23_4565057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 8].length) (baseStart_4565057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565057 prefixEnd_4565057 := by exact prefixLift 4565057
  have htrace : WordTrace (prefixWord ++ tailWord_4565057) baseStart_4565057 baseEnd_4565057 := by
    simpa [prefixWord, tailWord_4565057, baseEnd_4565057] using wordTrace_append hprefix tailTrace_4565057
  have hstable : (prefixWord ++ tailWord_4565057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565057).length < 2 ^ (prefixWord ++ tailWord_4565057).sum := by decide
  have hdescent : baseEnd_4565057 < baseStart_4565057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565085 : List Nat := [1, 4, 4, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_4565085 : Nat := 118140960795 + 4565085 * 2 ^ 59
def prefixEnd_4565085 : Nat := 4983230072969 + 3 ^ 40 * 4565085 * 2
def baseEnd_4565085 : Nat := 2344082833630376817643063

theorem tailTrace_4565085 : CollatzResearch.WordTrace tailWord_4565085 prefixEnd_4565085 2344082833630376817643063 := by
  unfold tailWord_4565085
  simp only [CollatzResearch.WordTrace]
  refine ⟨166502328666484174291648709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111001552444322782861099139 166502328666484174291648709)
  ·
    refine ⟨31219186624965782679684133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166502328666484174291648709 31219186624965782679684133)
    ·
      refine ⟨5853597492181084252440775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31219186624965782679684133 5853597492181084252440775)
      ·
        refine ⟨8780396238271626378661163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5853597492181084252440775 8780396238271626378661163)
        ·
          refine ⟨13170594357407439567991745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8780396238271626378661163 13170594357407439567991745)
          ·
            refine ⟨9877945768055579675993809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13170594357407439567991745 9877945768055579675993809)
            ·
              refine ⟨7408459326041684756995357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9877945768055579675993809 7408459326041684756995357)
              ·
                refine ⟨2778172247265631783873259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7408459326041684756995357 2778172247265631783873259)
                ·
                  refine ⟨4167258370898447675809889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2778172247265631783873259 4167258370898447675809889)
                  ·
                    refine ⟨3125443778173835756857417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4167258370898447675809889 3125443778173835756857417)
                    ·
                      refine ⟨2344082833630376817643063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3125443778173835756857417 2344082833630376817643063)
                      ·
                        rfl

theorem cell23_4565085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_4565085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565085 prefixEnd_4565085 := by exact prefixLift 4565085
  have htrace : WordTrace (prefixWord ++ tailWord_4565085) baseStart_4565085 baseEnd_4565085 := by
    simpa [prefixWord, tailWord_4565085, baseEnd_4565085] using wordTrace_append hprefix tailTrace_4565085
  have hstable : (prefixWord ++ tailWord_4565085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565085).length < 2 ^ (prefixWord ++ tailWord_4565085).sum := by decide
  have hdescent : baseEnd_4565085 < baseStart_4565085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565100 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 2, 6]
def baseStart_4565100 : Nat := 118140960795 + 4565100 * 2 ^ 59
def prefixEnd_4565100 : Nat := 4983230072969 + 3 ^ 40 * 4565100 * 2
def baseEnd_4565100 : Nat := 781363511946731419651831

theorem tailTrace_4565100 : CollatzResearch.WordTrace tailWord_4565100 prefixEnd_4565100 781363511946731419651831 := by
  unfold tailWord_4565100
  simp only [CollatzResearch.WordTrace]
  refine ⟨83251437880714915926722377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111001917174286554568963169 83251437880714915926722377)
  ·
    refine ⟨62438578410536186945041783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83251437880714915926722377 62438578410536186945041783)
    ·
      refine ⟨93657867615804280417562675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62438578410536186945041783 93657867615804280417562675)
      ·
        refine ⟨140486801423706420626344013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93657867615804280417562675 140486801423706420626344013)
        ·
          refine ⟨52682550533889907734879005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140486801423706420626344013 52682550533889907734879005)
          ·
            refine ⟨19755956450208715400579627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52682550533889907734879005 19755956450208715400579627)
            ·
              refine ⟨29633934675313073100869441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19755956450208715400579627 29633934675313073100869441)
              ·
                refine ⟨22225451006484804825652081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29633934675313073100869441 22225451006484804825652081)
                ·
                  refine ⟨16669088254863603619239061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22225451006484804825652081 16669088254863603619239061)
                  ·
                    refine ⟨781363511946731419651831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16669088254863603619239061 781363511946731419651831)
                    ·
                      rfl

theorem cell23_4565100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_4565100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565100 prefixEnd_4565100 := by exact prefixLift 4565100
  have htrace : WordTrace (prefixWord ++ tailWord_4565100) baseStart_4565100 baseEnd_4565100 := by
    simpa [prefixWord, tailWord_4565100, baseEnd_4565100] using wordTrace_append hprefix tailTrace_4565100
  have hstable : (prefixWord ++ tailWord_4565100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565100).length < 2 ^ (prefixWord ++ tailWord_4565100).sum := by decide
  have hdescent : baseEnd_4565100 < baseStart_4565100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565167 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 2, 5, 2]
def baseStart_4565167 : Nat := 118140960795 + 4565167 * 2 ^ 59
def prefixEnd_4565167 : Nat := 4983230072969 + 3 ^ 40 * 4565167 * 2
def baseEnd_4565167 : Nat := 2344124939044045496817685

theorem tailTrace_4565167 : CollatzResearch.WordTrace tailWord_4565167 prefixEnd_4565167 2344124939044045496817685 := by
  unfold tailWord_4565167
  simp only [CollatzResearch.WordTrace]
  refine ⟨166505319452187102296133755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111003546301458068197422503 166505319452187102296133755)
  ·
    refine ⟨249757979178280653444200633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166505319452187102296133755 249757979178280653444200633)
    ·
      refine ⟨187318484383710490083150475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249757979178280653444200633 187318484383710490083150475)
      ·
        refine ⟨280977726575565735124725713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187318484383710490083150475 280977726575565735124725713)
        ·
          refine ⟨210733294931674301343544285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280977726575565735124725713 210733294931674301343544285)
          ·
            refine ⟨79024985599377863003829107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210733294931674301343544285 79024985599377863003829107)
            ·
              refine ⟨118537478399066794505743661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79024985599377863003829107 118537478399066794505743661)
              ·
                refine ⟨44451554399650047939653873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118537478399066794505743661 44451554399650047939653873)
                ·
                  refine ⟨33338665799737535954740405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44451554399650047939653873 33338665799737535954740405)
                  ·
                    refine ⟨3125499918725393995756913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33338665799737535954740405 3125499918725393995756913)
                    ·
                      refine ⟨2344124939044045496817685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3125499918725393995756913 2344124939044045496817685)
                      ·
                        rfl

theorem cell23_4565167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 5, 2].length) (baseStart_4565167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565167 prefixEnd_4565167 := by exact prefixLift 4565167
  have htrace : WordTrace (prefixWord ++ tailWord_4565167) baseStart_4565167 baseEnd_4565167 := by
    simpa [prefixWord, tailWord_4565167, baseEnd_4565167] using wordTrace_append hprefix tailTrace_4565167
  have hstable : (prefixWord ++ tailWord_4565167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565167).length < 2 ^ (prefixWord ++ tailWord_4565167).sum := by decide
  have hdescent : baseEnd_4565167 < baseStart_4565167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565304 : List Nat := [2, 1, 2, 1, 3, 1, 3, 4, 1, 1, 4]
def baseStart_4565304 : Nat := 118140960795 + 4565304 * 2 ^ 59
def prefixEnd_4565304 : Nat := 4983230072969 + 3 ^ 40 * 4565304 * 2
def baseEnd_4565304 : Nat := 2344195285893711460804555

theorem tailTrace_4565304 : CollatzResearch.WordTrace tailWord_4565304 prefixEnd_4565304 2344195285893711460804555 := by
  unfold tailWord_4565304
  simp only [CollatzResearch.WordTrace]
  refine ⟨83255158126345387346935483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111006877501793849795913977 83255158126345387346935483)
  ·
    refine ⟨124882737189518081020403225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83255158126345387346935483 124882737189518081020403225)
    ·
      refine ⟨93662052892138560765302419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124882737189518081020403225 93662052892138560765302419)
      ·
        refine ⟨140493079338207841147953629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93662052892138560765302419 140493079338207841147953629)
        ·
          refine ⟨52684904751827940430482611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140493079338207841147953629 52684904751827940430482611)
          ·
            refine ⟨79027357127741910645723917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52684904751827940430482611 79027357127741910645723917)
            ·
              refine ⟨29635258922903216492146469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79027357127741910645723917 29635258922903216492146469)
              ·
                refine ⟨5556611048044353092277463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29635258922903216492146469 5556611048044353092277463)
                ·
                  refine ⟨8334916572066529638416195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5556611048044353092277463 8334916572066529638416195)
                  ·
                    refine ⟨12502374858099794457624293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8334916572066529638416195 12502374858099794457624293)
                    ·
                      refine ⟨2344195285893711460804555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12502374858099794457624293 2344195285893711460804555)
                      ·
                        rfl

theorem cell23_4565304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_4565304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565304 prefixEnd_4565304 := by exact prefixLift 4565304
  have htrace : WordTrace (prefixWord ++ tailWord_4565304) baseStart_4565304 baseEnd_4565304 := by
    simpa [prefixWord, tailWord_4565304, baseEnd_4565304] using wordTrace_append hprefix tailTrace_4565304
  have hstable : (prefixWord ++ tailWord_4565304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565304).length < 2 ^ (prefixWord ++ tailWord_4565304).sum := by decide
  have hdescent : baseEnd_4565304 < baseStart_4565304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565324 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 1, 1, 5]
def baseStart_4565324 : Nat := 118140960795 + 4565324 * 2 ^ 59
def prefixEnd_4565324 : Nat := 4983230072969 + 3 ^ 40 * 4565324 * 2
def baseEnd_4565324 : Nat := 2344205555506801382554463

theorem tailTrace_4565324 : CollatzResearch.WordTrace tailWord_4565324 prefixEnd_4565324 2344205555506801382554463 := by
  unfold tailWord_4565324
  simp only [CollatzResearch.WordTrace]
  refine ⟨83255522856309159054799513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111007363808412212073066017 83255522856309159054799513)
  ·
    refine ⟨62441642142231869291099635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83255522856309159054799513 62441642142231869291099635)
    ·
      refine ⟨93662463213347803936649453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62441642142231869291099635 93662463213347803936649453)
      ·
        refine ⟨35123423705005426476243545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93662463213347803936649453 35123423705005426476243545)
        ·
          refine ⟨26342567778754069857182659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35123423705005426476243545 26342567778754069857182659)
          ·
            refine ⟨39513851668131104785773989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26342567778754069857182659 39513851668131104785773989)
            ·
              refine ⟨7408847187774582147332623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39513851668131104785773989 7408847187774582147332623)
              ·
                refine ⟨11113270781661873220998935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7408847187774582147332623 11113270781661873220998935)
                ·
                  refine ⟨16669906172492809831498403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11113270781661873220998935 16669906172492809831498403)
                  ·
                    refine ⟨25004859258739214747247605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16669906172492809831498403 25004859258739214747247605)
                    ·
                      refine ⟨2344205555506801382554463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25004859258739214747247605 2344205555506801382554463)
                      ·
                        rfl

theorem cell23_4565324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_4565324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565324 prefixEnd_4565324 := by exact prefixLift 4565324
  have htrace : WordTrace (prefixWord ++ tailWord_4565324) baseStart_4565324 baseEnd_4565324 := by
    simpa [prefixWord, tailWord_4565324, baseEnd_4565324] using wordTrace_append hprefix tailTrace_4565324
  have hstable : (prefixWord ++ tailWord_4565324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565324).length < 2 ^ (prefixWord ++ tailWord_4565324).sum := by decide
  have hdescent : baseEnd_4565324 < baseStart_4565324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565344 : List Nat := [2, 1, 1, 3, 5, 1, 2, 8]
def baseStart_4565344 : Nat := 118140960795 + 4565344 * 2 ^ 59
def prefixEnd_4565344 : Nat := 4983230072969 + 3 ^ 40 * 4565344 * 2
def baseEnd_4565344 : Nat := 86822808337773752011273

theorem tailTrace_4565344 : CollatzResearch.WordTrace tailWord_4565344 prefixEnd_4565344 86822808337773752011273 := by
  unfold tailWord_4565344
  simp only [CollatzResearch.WordTrace]
  refine ⟨83255887586272930762663543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111007850115030574350218057 83255887586272930762663543)
  ·
    refine ⟨124883831379409396143995315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83255887586272930762663543 124883831379409396143995315)
    ·
      refine ⟨187325747069114094215992973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124883831379409396143995315 187325747069114094215992973)
      ·
        refine ⟨70247155150917785330997365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187325747069114094215992973 70247155150917785330997365)
        ·
          refine ⟨6585670795398542374781003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70247155150917785330997365 6585670795398542374781003)
          ·
            refine ⟨9878506193097813562171505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6585670795398542374781003 9878506193097813562171505)
            ·
              refine ⟨7408879644823360171628629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9878506193097813562171505 7408879644823360171628629)
              ·
                refine ⟨86822808337773752011273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7408879644823360171628629 86822808337773752011273)
                ·
                  rfl

theorem cell23_4565344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 8].length) (baseStart_4565344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565344 prefixEnd_4565344 := by exact prefixLift 4565344
  have htrace : WordTrace (prefixWord ++ tailWord_4565344) baseStart_4565344 baseEnd_4565344 := by
    simpa [prefixWord, tailWord_4565344, baseEnd_4565344] using wordTrace_append hprefix tailTrace_4565344
  have hstable : (prefixWord ++ tailWord_4565344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565344).length < 2 ^ (prefixWord ++ tailWord_4565344).sum := by decide
  have hdescent : baseEnd_4565344 < baseStart_4565344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565347 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 6]
def baseStart_4565347 : Nat := 118140960795 + 4565347 * 2 ^ 59
def prefixEnd_4565347 : Nat := 4983230072969 + 3 ^ 40 * 4565347 * 2
def baseEnd_4565347 : Nat := 2344217365561854792566857

theorem tailTrace_4565347 : CollatzResearch.WordTrace tailWord_4565347 prefixEnd_4565347 2344217365561854792566857 := by
  unfold tailWord_4565347
  simp only [CollatzResearch.WordTrace]
  refine ⟨166511884591534993037686295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111007923061023328691790863 166511884591534993037686295)
  ·
    refine ⟨249767826887302489556529443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166511884591534993037686295 249767826887302489556529443)
    ·
      refine ⟨374651740330953734334794165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249767826887302489556529443 374651740330953734334794165)
      ·
        refine ⟨35123600656026912593886953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 374651740330953734334794165 35123600656026912593886953)
        ·
          refine ⟨26342700492020184445415215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35123600656026912593886953 26342700492020184445415215)
          ·
            refine ⟨39514050738030276668122823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26342700492020184445415215 39514050738030276668122823)
            ·
              refine ⟨59271076107045415002184235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39514050738030276668122823 59271076107045415002184235)
              ·
                refine ⟨88906614160568122503276353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59271076107045415002184235 88906614160568122503276353)
                ·
                  refine ⟨66679960620426091877457265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88906614160568122503276353 66679960620426091877457265)
                  ·
                    refine ⟨50009970465319568908092949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66679960620426091877457265 50009970465319568908092949)
                    ·
                      refine ⟨2344217365561854792566857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50009970465319568908092949 2344217365561854792566857)
                      ·
                        rfl

theorem cell23_4565347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_4565347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565347 prefixEnd_4565347 := by exact prefixLift 4565347
  have htrace : WordTrace (prefixWord ++ tailWord_4565347) baseStart_4565347 baseEnd_4565347 := by
    simpa [prefixWord, tailWord_4565347, baseEnd_4565347] using wordTrace_append hprefix tailTrace_4565347
  have hstable : (prefixWord ++ tailWord_4565347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565347).length < 2 ^ (prefixWord ++ tailWord_4565347).sum := by decide
  have hdescent : baseEnd_4565347 < baseStart_4565347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565367 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 5]
def baseStart_4565367 : Nat := 118140960795 + 4565367 * 2 ^ 59
def prefixEnd_4565367 : Nat := 4983230072969 + 3 ^ 40 * 4565367 * 2
def baseEnd_4565367 : Nat := 2344227635174944714316765

theorem tailTrace_4565367 : CollatzResearch.WordTrace tailWord_4565367 prefixEnd_4565367 2344227635174944714316765 := by
  unfold tailWord_4565367
  simp only [CollatzResearch.WordTrace]
  refine ⟨166512614051462536453414355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111008409367641690968942903 166512614051462536453414355)
  ·
    refine ⟨249768921077193804680121533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166512614051462536453414355 249768921077193804680121533)
    ·
      refine ⟨93663345403947676755045575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249768921077193804680121533 93663345403947676755045575)
      ·
        refine ⟨140495018105921515132568363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93663345403947676755045575 140495018105921515132568363)
        ·
          refine ⟨210742527158882272698852545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140495018105921515132568363 210742527158882272698852545)
          ·
            refine ⟨158056895369161704524139409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210742527158882272698852545 158056895369161704524139409)
            ·
              refine ⟨118542671526871278393104557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158056895369161704524139409 118542671526871278393104557)
              ·
                refine ⟨44453501822576729397414209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118542671526871278393104557 44453501822576729397414209)
                ·
                  refine ⟨33340126366932547048060657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44453501822576729397414209 33340126366932547048060657)
                  ·
                    refine ⟨25005094775199410286045493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33340126366932547048060657 25005094775199410286045493)
                    ·
                      refine ⟨2344227635174944714316765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25005094775199410286045493 2344227635174944714316765)
                      ·
                        rfl

theorem cell23_4565367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_4565367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565367 prefixEnd_4565367 := by exact prefixLift 4565367
  have htrace : WordTrace (prefixWord ++ tailWord_4565367) baseStart_4565367 baseEnd_4565367 := by
    simpa [prefixWord, tailWord_4565367, baseEnd_4565367] using wordTrace_append hprefix tailTrace_4565367
  have hstable : (prefixWord ++ tailWord_4565367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565367).length < 2 ^ (prefixWord ++ tailWord_4565367).sum := by decide
  have hdescent : baseEnd_4565367 < baseStart_4565367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565388 : List Nat := [2, 2, 1, 2, 1, 5, 2, 2, 2, 1, 3]
def baseStart_4565388 : Nat := 118140960795 + 4565388 * 2 ^ 59
def prefixEnd_4565388 : Nat := 4983230072969 + 3 ^ 40 * 4565388 * 2
def baseEnd_4565388 : Nat := 2344238418268689132154169

theorem tailTrace_4565388 : CollatzResearch.WordTrace tailWord_4565388 prefixEnd_4565388 2344238418268689132154169 := by
  unfold tailWord_4565388
  simp only [CollatzResearch.WordTrace]
  refine ⟨83256689992193228519964409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111008919989590971359952545 83256689992193228519964409)
  ·
    refine ⟨62442517494144921389973307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83256689992193228519964409 62442517494144921389973307)
    ·
      refine ⟨93663776241217382084959961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62442517494144921389973307 93663776241217382084959961)
      ·
        refine ⟨70247832180913036563719971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93663776241217382084959961 70247832180913036563719971)
        ·
          refine ⟨105371748271369554845579957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70247832180913036563719971 105371748271369554845579957)
          ·
            refine ⟨9878601400440895766773121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105371748271369554845579957 9878601400440895766773121)
            ·
              refine ⟨7408951050330671825079841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9878601400440895766773121 7408951050330671825079841)
              ·
                refine ⟨5556713287748003868809881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7408951050330671825079841 5556713287748003868809881)
                ·
                  refine ⟨4167534965811002901607411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5556713287748003868809881 4167534965811002901607411)
                  ·
                    refine ⟨6251302448716504352411117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4167534965811002901607411 6251302448716504352411117)
                    ·
                      refine ⟨2344238418268689132154169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6251302448716504352411117 2344238418268689132154169)
                      ·
                        rfl

theorem cell23_4565388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_4565388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565388 prefixEnd_4565388 := by exact prefixLift 4565388
  have htrace : WordTrace (prefixWord ++ tailWord_4565388) baseStart_4565388 baseEnd_4565388 := by
    simpa [prefixWord, tailWord_4565388, baseEnd_4565388] using wordTrace_append hprefix tailTrace_4565388
  have hstable : (prefixWord ++ tailWord_4565388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565388).length < 2 ^ (prefixWord ++ tailWord_4565388).sum := by decide
  have hdescent : baseEnd_4565388 < baseStart_4565388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565411 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 1, 4, 2]
def baseStart_4565411 : Nat := 118140960795 + 4565411 * 2 ^ 59
def prefixEnd_4565411 : Nat := 4983230072969 + 3 ^ 40 * 4565411 * 2
def baseEnd_4565411 : Nat := 2344250228323742542166563

theorem tailTrace_4565411 : CollatzResearch.WordTrace tailWord_4565411 prefixEnd_4565411 2344250228323742542166563 := by
  unfold tailWord_4565411
  simp only [CollatzResearch.WordTrace]
  refine ⟨166514218863303131968016087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111009479242202087978677391 166514218863303131968016087)
  ·
    refine ⟨249771328294954697952024131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166514218863303131968016087 249771328294954697952024131)
    ·
      refine ⟨374656992442432046928036197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249771328294954697952024131 374656992442432046928036197)
      ·
        refine ⟨70248186082956008799006787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 374656992442432046928036197 70248186082956008799006787)
        ·
          refine ⟨105372279124434013198510181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70248186082956008799006787 105372279124434013198510181)
          ·
            refine ⟨19757302335831377474720659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105372279124434013198510181 19757302335831377474720659)
            ·
              refine ⟨29635953503747066212080989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19757302335831377474720659 29635953503747066212080989)
              ·
                refine ⟨11113482563905149829530371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29635953503747066212080989 11113482563905149829530371)
                ·
                  refine ⟨16670223845857724744295557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11113482563905149829530371 16670223845857724744295557)
                  ·
                    refine ⟨3125666971098323389555417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16670223845857724744295557 3125666971098323389555417)
                    ·
                      refine ⟨2344250228323742542166563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3125666971098323389555417 2344250228323742542166563)
                      ·
                        rfl

theorem cell23_4565411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_4565411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565411 prefixEnd_4565411 := by exact prefixLift 4565411
  have htrace : WordTrace (prefixWord ++ tailWord_4565411) baseStart_4565411 baseEnd_4565411 := by
    simpa [prefixWord, tailWord_4565411, baseEnd_4565411] using wordTrace_append hprefix tailTrace_4565411
  have hstable : (prefixWord ++ tailWord_4565411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565411).length < 2 ^ (prefixWord ++ tailWord_4565411).sum := by decide
  have hdescent : baseEnd_4565411 < baseStart_4565411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565427 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 7]
def baseStart_4565427 : Nat := 118140960795 + 4565427 * 2 ^ 59
def prefixEnd_4565427 : Nat := 4983230072969 + 3 ^ 40 * 4565427 * 2
def baseEnd_4565427 : Nat := 2344258444014214479566489

theorem tailTrace_4565427 : CollatzResearch.WordTrace tailWord_4565427 prefixEnd_4565427 2344258444014214479566489 := by
  unfold tailWord_4565427
  simp only [CollatzResearch.WordTrace]
  refine ⟨166514802431245166700598535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111009868287496777800399023 166514802431245166700598535)
  ·
    refine ⟨249772203646867750050897803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166514802431245166700598535 249772203646867750050897803)
    ·
      refine ⟨374658305470301625076346705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249772203646867750050897803 374658305470301625076346705)
      ·
        refine ⟨280993729102726218807260029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374658305470301625076346705 280993729102726218807260029)
        ·
          refine ⟨105372648413522332052722511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 280993729102726218807260029 105372648413522332052722511)
          ·
            refine ⟨158058972620283498079083767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105372648413522332052722511 158058972620283498079083767)
            ·
              refine ⟨237088458930425247118625651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158058972620283498079083767 237088458930425247118625651)
              ·
                refine ⟨355632688395637870677938477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237088458930425247118625651 355632688395637870677938477)
                ·
                  refine ⟨133362258148364201504226929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355632688395637870677938477 133362258148364201504226929)
                  ·
                    refine ⟨100021693611273151128170197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 133362258148364201504226929 100021693611273151128170197)
                    ·
                      refine ⟨2344258444014214479566489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100021693611273151128170197 2344258444014214479566489)
                      ·
                        rfl

theorem cell23_4565427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_4565427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565427 prefixEnd_4565427 := by exact prefixLift 4565427
  have htrace : WordTrace (prefixWord ++ tailWord_4565427) baseStart_4565427 baseEnd_4565427 := by
    simpa [prefixWord, tailWord_4565427, baseEnd_4565427] using wordTrace_append hprefix tailTrace_4565427
  have hstable : (prefixWord ++ tailWord_4565427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565427).length < 2 ^ (prefixWord ++ tailWord_4565427).sum := by decide
  have hdescent : baseEnd_4565427 < baseStart_4565427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565461 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 2, 3, 3]
def baseStart_4565461 : Nat := 118140960795 + 4565461 * 2 ^ 59
def prefixEnd_4565461 : Nat := 4983230072969 + 3 ^ 40 * 4565461 * 2
def baseEnd_4565461 : Nat := 2344275902356467346541333

theorem tailTrace_4565461 : CollatzResearch.WordTrace tailWord_4565461 prefixEnd_4565461 2344275902356467346541333 := by
  unfold tailWord_4565461
  simp only [CollatzResearch.WordTrace]
  refine ⟨166516042513121990507336237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111010695008747993671557491 166516042513121990507336237)
  ·
    refine ⟨62443515942420746440251089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166516042513121990507336237 62443515942420746440251089)
    ·
      refine ⟨46832636956815559830188317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62443515942420746440251089 46832636956815559830188317)
      ·
        refine ⟨17562238858805834936320619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46832636956815559830188317 17562238858805834936320619)
        ·
          refine ⟨26343358288208752404480929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17562238858805834936320619 26343358288208752404480929)
          ·
            refine ⟨19757518716156564303360697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26343358288208752404480929 19757518716156564303360697)
            ·
              refine ⟨14818139037117423227520523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19757518716156564303360697 14818139037117423227520523)
              ·
                refine ⟨22227208555676134841280785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14818139037117423227520523 22227208555676134841280785)
                ·
                  refine ⟨16670406416757101130960589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22227208555676134841280785 16670406416757101130960589)
                  ·
                    refine ⟨6251402406283912924110221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16670406416757101130960589 6251402406283912924110221)
                    ·
                      refine ⟨2344275902356467346541333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6251402406283912924110221 2344275902356467346541333)
                      ·
                        rfl

theorem cell23_4565461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_4565461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565461 prefixEnd_4565461 := by exact prefixLift 4565461
  have htrace : WordTrace (prefixWord ++ tailWord_4565461) baseStart_4565461 baseEnd_4565461 := by
    simpa [prefixWord, tailWord_4565461, baseEnd_4565461] using wordTrace_append hprefix tailTrace_4565461
  have hstable : (prefixWord ++ tailWord_4565461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565461).length < 2 ^ (prefixWord ++ tailWord_4565461).sum := by decide
  have hdescent : baseEnd_4565461 < baseStart_4565461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565484 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 4]
def baseStart_4565484 : Nat := 118140960795 + 4565484 * 2 ^ 59
def prefixEnd_4565484 : Nat := 4983230072969 + 3 ^ 40 * 4565484 * 2
def baseEnd_4565484 : Nat := 2344287712411520756553727

theorem tailTrace_4565484 : CollatzResearch.WordTrace tailWord_4565484 prefixEnd_4565484 2344287712411520756553727 := by
  unfold tailWord_4565484
  simp only [CollatzResearch.WordTrace]
  refine ⟨83258440696019332717711753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111011254261359110290282337 83258440696019332717711753)
  ·
    refine ⟨62443830522014499538283815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83258440696019332717711753 62443830522014499538283815)
    ·
      refine ⟨93665745783021749307425723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62443830522014499538283815 93665745783021749307425723)
      ·
        refine ⟨140498618674532623961138585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93665745783021749307425723 140498618674532623961138585)
        ·
          refine ⟨105373964005899467970853939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140498618674532623961138585 105373964005899467970853939)
          ·
            refine ⟨158060946008849201956280909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105373964005899467970853939 158060946008849201956280909)
            ·
              refine ⟨59272854753318450733605341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158060946008849201956280909 59272854753318450733605341)
              ·
                refine ⟨22227320532494419025102003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59272854753318450733605341 22227320532494419025102003)
                ·
                  refine ⟨33340980798741628537653005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22227320532494419025102003 33340980798741628537653005)
                  ·
                    refine ⟨12502867799528110701619877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33340980798741628537653005 12502867799528110701619877)
                    ·
                      refine ⟨2344287712411520756553727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12502867799528110701619877 2344287712411520756553727)
                      ·
                        rfl

theorem cell23_4565484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_4565484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565484 prefixEnd_4565484 := by exact prefixLift 4565484
  have htrace : WordTrace (prefixWord ++ tailWord_4565484) baseStart_4565484 baseEnd_4565484 := by
    simpa [prefixWord, tailWord_4565484, baseEnd_4565484] using wordTrace_append hprefix tailTrace_4565484
  have hstable : (prefixWord ++ tailWord_4565484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565484).length < 2 ^ (prefixWord ++ tailWord_4565484).sum := by decide
  have hdescent : baseEnd_4565484 < baseStart_4565484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565485 : List Nat := [1, 5, 1, 3, 1, 3, 1, 3, 5]
def baseStart_4565485 : Nat := 118140960795 + 4565485 * 2 ^ 59
def prefixEnd_4565485 : Nat := 4983230072969 + 3 ^ 40 * 4565485 * 2
def baseEnd_4565485 : Nat := 260476469543575028071247

theorem tailTrace_4565485 : CollatzResearch.WordTrace tailWord_4565485 prefixEnd_4565485 260476469543575028071247 := by
  unfold tailWord_4565485
  simp only [CollatzResearch.WordTrace]
  refine ⟨166516917865035042606209909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111011278576690028404139939 166516917865035042606209909)
  ·
    refine ⟨15610961049847035244332179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166516917865035042606209909 15610961049847035244332179)
    ·
      refine ⟨23416441574770552866498269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15610961049847035244332179 23416441574770552866498269)
      ·
        refine ⟨8781165590538957324936851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23416441574770552866498269 8781165590538957324936851)
        ·
          refine ⟨13171748385808435987405277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8781165590538957324936851 13171748385808435987405277)
          ·
            refine ⟨4939405644678163495276979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13171748385808435987405277 4939405644678163495276979)
            ·
              refine ⟨7409108467017245242915469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4939405644678163495276979 7409108467017245242915469)
              ·
                refine ⟨2778415675131466966093301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7409108467017245242915469 2778415675131466966093301)
                ·
                  refine ⟨260476469543575028071247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2778415675131466966093301 260476469543575028071247)
                  ·
                    rfl

theorem cell23_4565485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_4565485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565485 prefixEnd_4565485 := by exact prefixLift 4565485
  have htrace : WordTrace (prefixWord ++ tailWord_4565485) baseStart_4565485 baseEnd_4565485 := by
    simpa [prefixWord, tailWord_4565485, baseEnd_4565485] using wordTrace_append hprefix tailTrace_4565485
  have hstable : (prefixWord ++ tailWord_4565485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565485).length < 2 ^ (prefixWord ++ tailWord_4565485).sum := by decide
  have hdescent : baseEnd_4565485 < baseStart_4565485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565501 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_4565501 : Nat := 118140960795 + 4565501 * 2 ^ 59
def prefixEnd_4565501 : Nat := 4983230072969 + 3 ^ 40 * 4565501 * 2
def baseEnd_4565501 : Nat := 2344296441582647190041149

theorem tailTrace_4565501 : CollatzResearch.WordTrace tailWord_4565501 prefixEnd_4565501 2344296441582647190041149 := by
  unfold tailWord_4565501
  simp only [CollatzResearch.WordTrace]
  refine ⟨166517501432977077338792357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111011667621984718225861571 166517501432977077338792357)
  ·
    refine ⟨31222031518683202001023567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166517501432977077338792357 31222031518683202001023567)
    ·
      refine ⟨46833047278024803001535351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31222031518683202001023567 46833047278024803001535351)
      ·
        refine ⟨70249570917037204502303027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46833047278024803001535351 70249570917037204502303027)
        ·
          refine ⟨105374356375555806753454541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70249570917037204502303027 105374356375555806753454541)
          ·
            refine ⟨39515383640833427532545453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105374356375555806753454541 39515383640833427532545453)
            ·
              refine ⟨14818268865312535324704545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39515383640833427532545453 14818268865312535324704545)
              ·
                refine ⟨11113701648984401493528409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14818268865312535324704545 11113701648984401493528409)
                ·
                  refine ⟨8335276236738301120146307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11113701648984401493528409 8335276236738301120146307)
                  ·
                    refine ⟨12502914355107451680219461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8335276236738301120146307 12502914355107451680219461)
                    ·
                      refine ⟨2344296441582647190041149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12502914355107451680219461 2344296441582647190041149)
                      ·
                        rfl

theorem cell23_4565501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_4565501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565501 prefixEnd_4565501 := by exact prefixLift 4565501
  have htrace : WordTrace (prefixWord ++ tailWord_4565501) baseStart_4565501 baseEnd_4565501 := by
    simpa [prefixWord, tailWord_4565501, baseEnd_4565501] using wordTrace_append hprefix tailTrace_4565501
  have hstable : (prefixWord ++ tailWord_4565501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565501).length < 2 ^ (prefixWord ++ tailWord_4565501).sum := by decide
  have hdescent : baseEnd_4565501 < baseStart_4565501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565504 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 3]
def baseStart_4565504 : Nat := 118140960795 + 4565504 * 2 ^ 59
def prefixEnd_4565504 : Nat := 4983230072969 + 3 ^ 40 * 4565504 * 2
def baseEnd_4565504 : Nat := 2344297982024610678303635

theorem tailTrace_4565504 : CollatzResearch.WordTrace tailWord_4565504 prefixEnd_4565504 2344297982024610678303635 := by
  unfold tailWord_4565504
  simp only [CollatzResearch.WordTrace]
  refine ⟨83258805425983104425575783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111011740567977472567434377 83258805425983104425575783)
  ·
    refine ⟨124888208138974656638363675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83258805425983104425575783 124888208138974656638363675)
    ·
      refine ⟨187332312208461984957545513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124888208138974656638363675 187332312208461984957545513)
      ·
        refine ⟨140499234156346488718159135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187332312208461984957545513 140499234156346488718159135)
        ·
          refine ⟨210748851234519733077238703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140499234156346488718159135 210748851234519733077238703)
          ·
            refine ⟨316123276851779599615858055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210748851234519733077238703 316123276851779599615858055)
            ·
              refine ⟨474184915277669399423787083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316123276851779599615858055 474184915277669399423787083)
              ·
                refine ⟨711277372916504099135680625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474184915277669399423787083 711277372916504099135680625)
                ·
                  refine ⟨533458029687378074351760469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 711277372916504099135680625 533458029687378074351760469)
                  ·
                    refine ⟨6251461285398961808809693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 533458029687378074351760469 6251461285398961808809693)
                    ·
                      refine ⟨2344297982024610678303635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6251461285398961808809693 2344297982024610678303635)
                      ·
                        rfl

theorem cell23_4565504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_4565504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565504 prefixEnd_4565504 := by exact prefixLift 4565504
  have htrace : WordTrace (prefixWord ++ tailWord_4565504) baseStart_4565504 baseEnd_4565504 := by
    simpa [prefixWord, tailWord_4565504, baseEnd_4565504] using wordTrace_append hprefix tailTrace_4565504
  have hstable : (prefixWord ++ tailWord_4565504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565504).length < 2 ^ (prefixWord ++ tailWord_4565504).sum := by decide
  have hdescent : baseEnd_4565504 < baseStart_4565504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565558 : List Nat := [5, 1, 2, 1, 2, 1, 1, 4, 6]
def baseStart_4565558 : Nat := 118140960795 + 4565558 * 2 ^ 59
def prefixEnd_4565558 : Nat := 4983230072969 + 3 ^ 40 * 4565558 * 2
def baseEnd_4565558 : Nat := 260480634442217051892043

theorem tailTrace_4565558 : CollatzResearch.WordTrace tailWord_4565558 prefixEnd_4565558 260480634442217051892043 := by
  unfold tailWord_4565558
  simp only [CollatzResearch.WordTrace]
  refine ⟨10407473774610661004601083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111013053595847050715744885 10407473774610661004601083)
  ·
    refine ⟨15611210661915991506901625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10407473774610661004601083 15611210661915991506901625)
    ·
      refine ⟨11708407996436993630176219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15611210661915991506901625 11708407996436993630176219)
      ·
        refine ⟨17562611994655490445264329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11708407996436993630176219 17562611994655490445264329)
        ·
          refine ⟨13171958995991617833948247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17562611994655490445264329 13171958995991617833948247)
          ·
            refine ⟨19757938493987426750922371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13171958995991617833948247 19757938493987426750922371)
            ·
              refine ⟨29636907740981140126383557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19757938493987426750922371 29636907740981140126383557)
              ·
                refine ⟨5556920201433963773696917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29636907740981140126383557 5556920201433963773696917)
                ·
                  refine ⟨260480634442217051892043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5556920201433963773696917 260480634442217051892043)
                  ·
                    rfl

theorem cell23_4565558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_4565558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565558 prefixEnd_4565558 := by exact prefixLift 4565558
  have htrace : WordTrace (prefixWord ++ tailWord_4565558) baseStart_4565558 baseEnd_4565558 := by
    simpa [prefixWord, tailWord_4565558, baseEnd_4565558] using wordTrace_append hprefix tailTrace_4565558
  have hstable : (prefixWord ++ tailWord_4565558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565558).length < 2 ^ (prefixWord ++ tailWord_4565558).sum := by decide
  have hdescent : baseEnd_4565558 < baseStart_4565558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565562 : List Nat := [3, 1, 1, 1, 3, 5, 2, 2, 1, 4]
def baseStart_4565562 : Nat := 118140960795 + 4565562 * 2 ^ 59
def prefixEnd_4565562 : Nat := 4983230072969 + 3 ^ 40 * 4565562 * 2
def baseEnd_4565562 : Nat := 781442587967523817126123

theorem tailTrace_4565562 : CollatzResearch.WordTrace tailWord_4565562 prefixEnd_4565562 781442587967523817126123 := by
  unfold tailWord_4565562
  simp only [CollatzResearch.WordTrace]
  refine ⟨41629931571439021189190735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111013150857170723171175293 41629931571439021189190735)
  ·
    refine ⟨62444897357158531783786103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41629931571439021189190735 62444897357158531783786103)
    ·
      refine ⟨93667346035737797675679155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62444897357158531783786103 93667346035737797675679155)
      ·
        refine ⟨140501019053606696513518733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93667346035737797675679155 140501019053606696513518733)
        ·
          refine ⟨52687882145102511192569525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140501019053606696513518733 52687882145102511192569525)
          ·
            refine ⟨4939488951103360424303393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52687882145102511192569525 4939488951103360424303393)
            ·
              refine ⟨3704616713327520318227545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4939488951103360424303393 3704616713327520318227545)
              ·
                refine ⟨2778462534995640238670659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3704616713327520318227545 2778462534995640238670659)
                ·
                  refine ⟨4167693802493460358005989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2778462534995640238670659 4167693802493460358005989)
                  ·
                    refine ⟨781442587967523817126123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4167693802493460358005989 781442587967523817126123)
                    ·
                      rfl

theorem cell23_4565562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 1, 4].length) (baseStart_4565562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565562 prefixEnd_4565562 := by exact prefixLift 4565562
  have htrace : WordTrace (prefixWord ++ tailWord_4565562) baseStart_4565562 baseEnd_4565562 := by
    simpa [prefixWord, tailWord_4565562, baseEnd_4565562] using wordTrace_append hprefix tailTrace_4565562
  have hstable : (prefixWord ++ tailWord_4565562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565562).length < 2 ^ (prefixWord ++ tailWord_4565562).sum := by decide
  have hdescent : baseEnd_4565562 < baseStart_4565562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565591 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 4]
def baseStart_4565591 : Nat := 118140960795 + 4565591 * 2 ^ 59
def prefixEnd_4565591 : Nat := 4983230072969 + 3 ^ 40 * 4565591 * 2
def baseEnd_4565591 : Nat := 2344342654841551837915735

theorem tailTrace_4565591 : CollatzResearch.WordTrace tailWord_4565591 prefixEnd_4565591 2344342654841551837915735 := by
  unfold tailWord_4565591
  simp only [CollatzResearch.WordTrace]
  refine ⟨166520784002651022709568627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111013856001767348473045751 166520784002651022709568627)
  ·
    refine ⟨249781176003976534064352941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166520784002651022709568627 249781176003976534064352941)
    ·
      refine ⟨93667941001491200274132353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249781176003976534064352941 93667941001491200274132353)
      ·
        refine ⟨70250955751118400205599265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93667941001491200274132353 70250955751118400205599265)
        ·
          refine ⟨52688216813338800154199449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70250955751118400205599265 52688216813338800154199449)
          ·
            refine ⟨39516162610004100115649587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52688216813338800154199449 39516162610004100115649587)
            ·
              refine ⟨59274243915006150173474381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39516162610004100115649587 59274243915006150173474381)
              ·
                refine ⟨22227841468127306315052893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59274243915006150173474381 22227841468127306315052893)
                ·
                  refine ⟨8335440550547739868144835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22227841468127306315052893 8335440550547739868144835)
                  ·
                    refine ⟨12503160825821609802217253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8335440550547739868144835 12503160825821609802217253)
                    ·
                      refine ⟨2344342654841551837915735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12503160825821609802217253 2344342654841551837915735)
                      ·
                        rfl

theorem cell23_4565591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_4565591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565591 prefixEnd_4565591 := by exact prefixLift 4565591
  have htrace : WordTrace (prefixWord ++ tailWord_4565591) baseStart_4565591 baseEnd_4565591 := by
    simpa [prefixWord, tailWord_4565591, baseEnd_4565591] using wordTrace_append hprefix tailTrace_4565591
  have hstable : (prefixWord ++ tailWord_4565591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565591).length < 2 ^ (prefixWord ++ tailWord_4565591).sum := by decide
  have hdescent : baseEnd_4565591 < baseStart_4565591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565601 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 1, 6]
def baseStart_4565601 : Nat := 118140960795 + 4565601 * 2 ^ 59
def prefixEnd_4565601 : Nat := 4983230072969 + 3 ^ 40 * 4565601 * 2
def baseEnd_4565601 : Nat := 781449263216032266263563

theorem tailTrace_4565601 : CollatzResearch.WordTrace tailWord_4565601 prefixEnd_4565601 781449263216032266263563 := by
  unfold tailWord_4565601
  simp only [CollatzResearch.WordTrace]
  refine ⟨166521148732614794417432657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111014099155076529611621771 166521148732614794417432657)
  ·
    refine ⟨124890861549461095813074493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166521148732614794417432657 124890861549461095813074493)
    ·
      refine ⟨46834073081047910929902935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124890861549461095813074493 46834073081047910929902935)
      ·
        refine ⟨70251109621571866394854403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46834073081047910929902935 70251109621571866394854403)
        ·
          refine ⟨105376664432357799592281605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70251109621571866394854403 105376664432357799592281605)
          ·
            refine ⟨19758124581067087423552801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105376664432357799592281605 19758124581067087423552801)
            ·
              refine ⟨14818593435800315567664601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19758124581067087423552801 14818593435800315567664601)
              ·
                refine ⟨11113945076850236675748451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14818593435800315567664601 11113945076850236675748451)
                ·
                  refine ⟨16670917615275355013622677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11113945076850236675748451 16670917615275355013622677)
                  ·
                    refine ⟨781449263216032266263563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16670917615275355013622677 781449263216032266263563)
                    ·
                      rfl

theorem cell23_4565601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_4565601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565601 prefixEnd_4565601 := by exact prefixLift 4565601
  have htrace : WordTrace (prefixWord ++ tailWord_4565601) baseStart_4565601 baseEnd_4565601 := by
    simpa [prefixWord, tailWord_4565601, baseEnd_4565601] using wordTrace_append hprefix tailTrace_4565601
  have hstable : (prefixWord ++ tailWord_4565601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565601).length < 2 ^ (prefixWord ++ tailWord_4565601).sum := by decide
  have hdescent : baseEnd_4565601 < baseStart_4565601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565611 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 3]
def baseStart_4565611 : Nat := 118140960795 + 4565611 * 2 ^ 59
def prefixEnd_4565611 : Nat := 4983230072969 + 3 ^ 40 * 4565611 * 2
def baseEnd_4565611 : Nat := 2344352924454641759665643

theorem tailTrace_4565611 : CollatzResearch.WordTrace tailWord_4565611 prefixEnd_4565611 2344352924454641759665643 := by
  unfold tailWord_4565611
  simp only [CollatzResearch.WordTrace]
  refine ⟨166521513462578566125296687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111014342308385710750197791 166521513462578566125296687)
  ·
    refine ⟨249782270193867849187945031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166521513462578566125296687 249782270193867849187945031)
    ·
      refine ⟨374673405290801773781917547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249782270193867849187945031 374673405290801773781917547)
      ·
        refine ⟨562010107936202660672876321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374673405290801773781917547 562010107936202660672876321)
        ·
          refine ⟨421507580952151995504657241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 562010107936202660672876321 421507580952151995504657241)
          ·
            refine ⟨316130685714113996628492931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421507580952151995504657241 316130685714113996628492931)
            ·
              refine ⟨474196028571170994942739397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316130685714113996628492931 474196028571170994942739397)
              ·
                refine ⟨88911755357094561551763637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 474196028571170994942739397 88911755357094561551763637)
                ·
                  refine ⟨8335477064727615145477841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88911755357094561551763637 8335477064727615145477841)
                  ·
                    refine ⟨6251607798545711359108381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8335477064727615145477841 6251607798545711359108381)
                    ·
                      refine ⟨2344352924454641759665643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6251607798545711359108381 2344352924454641759665643)
                      ·
                        rfl

theorem cell23_4565611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 3].length) (baseStart_4565611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565611 prefixEnd_4565611 := by exact prefixLift 4565611
  have htrace : WordTrace (prefixWord ++ tailWord_4565611) baseStart_4565611 baseEnd_4565611 := by
    simpa [prefixWord, tailWord_4565611, baseEnd_4565611] using wordTrace_append hprefix tailTrace_4565611
  have hstable : (prefixWord ++ tailWord_4565611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565611).length < 2 ^ (prefixWord ++ tailWord_4565611).sum := by decide
  have hdescent : baseEnd_4565611 < baseStart_4565611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565625 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 3, 2, 2]
def baseStart_4565625 : Nat := 118140960795 + 4565625 * 2 ^ 59
def prefixEnd_4565625 : Nat := 4983230072969 + 3 ^ 40 * 4565625 * 2
def baseEnd_4565625 : Nat := 2344360113183804704890579

theorem tailTrace_4565625 : CollatzResearch.WordTrace tailWord_4565625 prefixEnd_4565625 2344360113183804704890579 := by
  unfold tailWord_4565625
  simp only [CollatzResearch.WordTrace]
  refine ⟨166522024084527846516306329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111014682723018564344204219 166522024084527846516306329)
  ·
    refine ⟨124891518063395884887229747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166522024084527846516306329 124891518063395884887229747)
    ·
      refine ⟨187337277095093827330844621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124891518063395884887229747 187337277095093827330844621)
      ·
        refine ⟨70251478910660185249066733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187337277095093827330844621 70251478910660185249066733)
        ·
          refine ⟨26344304591497569468400025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70251478910660185249066733 26344304591497569468400025)
          ·
            refine ⟨19758228443623177101300019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26344304591497569468400025 19758228443623177101300019)
            ·
              refine ⟨29637342665434765651950029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19758228443623177101300019 29637342665434765651950029)
              ·
                refine ⟨11114003499538037119481261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29637342665434765651950029 11114003499538037119481261)
                ·
                  refine ⟨4167751312326763919805473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11114003499538037119481261 4167751312326763919805473)
                  ·
                    refine ⟨3125813484245072939854105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4167751312326763919805473 3125813484245072939854105)
                    ·
                      refine ⟨2344360113183804704890579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3125813484245072939854105 2344360113183804704890579)
                      ·
                        rfl

theorem cell23_4565625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_4565625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565625 prefixEnd_4565625 := by exact prefixLift 4565625
  have htrace : WordTrace (prefixWord ++ tailWord_4565625) baseStart_4565625 baseEnd_4565625 := by
    simpa [prefixWord, tailWord_4565625, baseEnd_4565625] using wordTrace_append hprefix tailTrace_4565625
  have hstable : (prefixWord ++ tailWord_4565625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565625).length < 2 ^ (prefixWord ++ tailWord_4565625).sum := by decide
  have hdescent : baseEnd_4565625 < baseStart_4565625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565686 : List Nat := [5, 1, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_4565686 : Nat := 118140960795 + 4565686 * 2 ^ 59
def prefixEnd_4565686 : Nat := 4983230072969 + 3 ^ 40 * 4565686 * 2
def baseEnd_4565686 : Nat := 781463811834576322075933

theorem tailTrace_4565686 : CollatzResearch.WordTrace tailWord_4565686 prefixEnd_4565686 781463811834576322075933 := by
  unfold tailWord_4565686
  simp only [CollatzResearch.WordTrace]
  refine ⟨10407765558581678370892307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111016165958204569289517941 10407765558581678370892307)
  ·
    refine ⟨15611648337872517556338461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10407765558581678370892307 15611648337872517556338461)
    ·
      refine ⟨5854368126702194083626923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15611648337872517556338461 5854368126702194083626923)
      ·
        refine ⟨8781552190053291125440385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5854368126702194083626923 8781552190053291125440385)
        ·
          refine ⟨6586164142539968344080289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8781552190053291125440385 6586164142539968344080289)
          ·
            refine ⟨4939623106904976258060217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6586164142539968344080289 4939623106904976258060217)
            ·
              refine ⟨3704717330178732193545163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4939623106904976258060217 3704717330178732193545163)
              ·
                refine ⟨5557075995268098290317745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3704717330178732193545163 5557075995268098290317745)
                ·
                  refine ⟨4167806996451073717738309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5557075995268098290317745 4167806996451073717738309)
                  ·
                    refine ⟨781463811834576322075933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4167806996451073717738309 781463811834576322075933)
                    ·
                      rfl

theorem cell23_4565686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_4565686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565686 prefixEnd_4565686 := by exact prefixLift 4565686
  have htrace : WordTrace (prefixWord ++ tailWord_4565686) baseStart_4565686 baseEnd_4565686 := by
    simpa [prefixWord, tailWord_4565686, baseEnd_4565686] using wordTrace_append hprefix tailTrace_4565686
  have hstable : (prefixWord ++ tailWord_4565686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565686).length < 2 ^ (prefixWord ++ tailWord_4565686).sum := by decide
  have hdescent : baseEnd_4565686 < baseStart_4565686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565711 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 4]
def baseStart_4565711 : Nat := 118140960795 + 4565711 * 2 ^ 59
def prefixEnd_4565711 : Nat := 4983230072969 + 3 ^ 40 * 4565711 * 2
def baseEnd_4565711 : Nat := 2344404272520091368415183

theorem tailTrace_4565711 : CollatzResearch.WordTrace tailWord_4565711 prefixEnd_4565711 2344404272520091368415183 := by
  unfold tailWord_4565711
  simp only [CollatzResearch.WordTrace]
  refine ⟨166525160762216283203936987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111016773841477522135957991 166525160762216283203936987)
  ·
    refine ⟨249787741143324424805905481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166525160762216283203936987 249787741143324424805905481)
    ·
      refine ⟨187340805857493318604429111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249787741143324424805905481 187340805857493318604429111)
      ·
        refine ⟨281011208786239977906643667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187340805857493318604429111 281011208786239977906643667)
        ·
          refine ⟨421516813179359966859965501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281011208786239977906643667 421516813179359966859965501)
          ·
            refine ⟨158068804942259987572487063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 421516813179359966859965501 158068804942259987572487063)
            ·
              refine ⟨237103207413389981358730595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158068804942259987572487063 237103207413389981358730595)
              ·
                refine ⟨355654811120084972038095893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237103207413389981358730595 355654811120084972038095893)
                ·
                  refine ⟨16671319271253983064285745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 355654811120084972038095893 16671319271253983064285745)
                  ·
                    refine ⟨12503489453440487298214309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16671319271253983064285745 12503489453440487298214309)
                    ·
                      refine ⟨2344404272520091368415183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12503489453440487298214309 2344404272520091368415183)
                      ·
                        rfl

theorem cell23_4565711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_4565711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565711 prefixEnd_4565711 := by exact prefixLift 4565711
  have htrace : WordTrace (prefixWord ++ tailWord_4565711) baseStart_4565711 baseEnd_4565711 := by
    simpa [prefixWord, tailWord_4565711, baseEnd_4565711] using wordTrace_append hprefix tailTrace_4565711
  have hstable : (prefixWord ++ tailWord_4565711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565711).length < 2 ^ (prefixWord ++ tailWord_4565711).sum := by decide
  have hdescent : baseEnd_4565711 < baseStart_4565711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565732 : List Nat := [2, 3, 1, 1, 1, 4, 1, 4, 2, 2, 2]
def baseStart_4565732 : Nat := 118140960795 + 4565732 * 2 ^ 59
def prefixEnd_4565732 : Nat := 4983230072969 + 3 ^ 40 * 4565732 * 2
def baseEnd_4565732 : Nat := 2344415055613835786252587

theorem tailTrace_4565732 : CollatzResearch.WordTrace tailWord_4565732 prefixEnd_4565732 2344415055613835786252587 := by
  unfold tailWord_4565732
  simp only [CollatzResearch.WordTrace]
  refine ⟨83262963347570101895225725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111017284463426802526967633 83262963347570101895225725)
  ·
    refine ⟨31223611255338788210709647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83262963347570101895225725 31223611255338788210709647)
    ·
      refine ⟨46835416883008182316064471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31223611255338788210709647 46835416883008182316064471)
      ·
        refine ⟨70253125324512273474096707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46835416883008182316064471 70253125324512273474096707)
        ·
          refine ⟨105379687986768410211145061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70253125324512273474096707 105379687986768410211145061)
          ·
            refine ⟨19758691497519076914589699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105379687986768410211145061 19758691497519076914589699)
            ·
              refine ⟨29638037246278615371884549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19758691497519076914589699 29638037246278615371884549)
              ·
                refine ⟨5557131983677240382228353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29638037246278615371884549 5557131983677240382228353)
                ·
                  refine ⟨4167848987757930286671265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5557131983677240382228353 4167848987757930286671265)
                  ·
                    refine ⟨3125886740818447715003449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4167848987757930286671265 3125886740818447715003449)
                    ·
                      refine ⟨2344415055613835786252587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3125886740818447715003449 2344415055613835786252587)
                      ·
                        rfl

theorem cell23_4565732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_4565732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565732 prefixEnd_4565732 := by exact prefixLift 4565732
  have htrace : WordTrace (prefixWord ++ tailWord_4565732) baseStart_4565732 baseEnd_4565732 := by
    simpa [prefixWord, tailWord_4565732, baseEnd_4565732] using wordTrace_append hprefix tailTrace_4565732
  have hstable : (prefixWord ++ tailWord_4565732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565732).length < 2 ^ (prefixWord ++ tailWord_4565732).sum := by decide
  have hdescent : baseEnd_4565732 < baseStart_4565732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565751 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 1, 7]
def baseStart_4565751 : Nat := 118140960795 + 4565751 * 2 ^ 59
def prefixEnd_4565751 : Nat := 4983230072969 + 3 ^ 40 * 4565751 * 2
def baseEnd_4565751 : Nat := 781474937248757070638333

theorem tailTrace_4565751 : CollatzResearch.WordTrace tailWord_4565751 prefixEnd_4565751 781474937248757070638333 := by
  unfold tailWord_4565751
  simp only [CollatzResearch.WordTrace]
  refine ⟨166526619682071370035393107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111017746454714246690262071 166526619682071370035393107)
  ·
    refine ⟨249789929523107055053089661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166526619682071370035393107 249789929523107055053089661)
    ·
      refine ⟨93671223571165145644908623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249789929523107055053089661 93671223571165145644908623)
      ·
        refine ⟨140506835356747718467362935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93671223571165145644908623 140506835356747718467362935)
        ·
          refine ⟨210760253035121577701044403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140506835356747718467362935 210760253035121577701044403)
          ·
            refine ⟨316140379552682366551566605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210760253035121577701044403 316140379552682366551566605)
            ·
              refine ⟨118552642332255887456837477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 316140379552682366551566605 118552642332255887456837477)
              ·
                refine ⟨22228620437297978898157027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118552642332255887456837477 22228620437297978898157027)
                ·
                  refine ⟨33342930655946968347235541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22228620437297978898157027 33342930655946968347235541)
                  ·
                    refine ⟨781474937248757070638333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33342930655946968347235541 781474937248757070638333)
                    ·
                      rfl

theorem cell23_4565751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_4565751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565751 prefixEnd_4565751 := by exact prefixLift 4565751
  have htrace : WordTrace (prefixWord ++ tailWord_4565751) baseStart_4565751 baseEnd_4565751 := by
    simpa [prefixWord, tailWord_4565751, baseEnd_4565751] using wordTrace_append hprefix tailTrace_4565751
  have hstable : (prefixWord ++ tailWord_4565751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565751).length < 2 ^ (prefixWord ++ tailWord_4565751).sum := by decide
  have hdescent : baseEnd_4565751 < baseStart_4565751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565768 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 1, 7]
def baseStart_4565768 : Nat := 118140960795 + 4565768 * 2 ^ 59
def prefixEnd_4565768 : Nat := 4983230072969 + 3 ^ 40 * 4565768 * 2
def baseEnd_4565768 : Nat := 781477846972465881800807

theorem tailTrace_4565768 : CollatzResearch.WordTrace tailWord_4565768 prefixEnd_4565768 781477846972465881800807 := by
  unfold tailWord_4565768
  simp only [CollatzResearch.WordTrace]
  refine ⟨83263619861504890969380979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111018159815339854625841305 83263619861504890969380979)
  ·
    refine ⟨124895429792257336454071469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83263619861504890969380979 124895429792257336454071469)
    ·
      refine ⟨46835786172096501170276801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124895429792257336454071469 46835786172096501170276801)
      ·
        refine ⟨35126839629072375877707601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46835786172096501170276801 35126839629072375877707601)
        ·
          refine ⟨26345129721804281908280701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35126839629072375877707601 26345129721804281908280701)
          ·
            refine ⟨9879423645676605715605263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26345129721804281908280701 9879423645676605715605263)
            ·
              refine ⟨14819135468514908573407895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9879423645676605715605263 14819135468514908573407895)
              ·
                refine ⟨22228703202772362860111843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14819135468514908573407895 22228703202772362860111843)
                ·
                  refine ⟨33343054804158544290167765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22228703202772362860111843 33343054804158544290167765)
                  ·
                    refine ⟨781477846972465881800807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33343054804158544290167765 781477846972465881800807)
                    ·
                      rfl

theorem cell23_4565768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_4565768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565768 prefixEnd_4565768 := by exact prefixLift 4565768
  have htrace : WordTrace (prefixWord ++ tailWord_4565768) baseStart_4565768 baseEnd_4565768 := by
    simpa [prefixWord, tailWord_4565768, baseEnd_4565768] using wordTrace_append hprefix tailTrace_4565768
  have hstable : (prefixWord ++ tailWord_4565768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565768).length < 2 ^ (prefixWord ++ tailWord_4565768).sum := by decide
  have hdescent : baseEnd_4565768 < baseStart_4565768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
