import V185TrunkScan23Chunk0272

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1615300 : List Nat := [2, 3, 3, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_1615300 : Nat := 118140960795 + 1615300 * 2 ^ 59
def prefixEnd_1615300 : Nat := 4983230072969 + 3 ^ 40 * 1615300 * 2
def baseEnd_1615300 : Nat := 829425301207635365021377

theorem tailTrace_1615300 : CollatzResearch.WordTrace tailWord_1615300 prefixEnd_1615300 829425301207635365021377 := by
  unfold tailWord_1615300
  simp only [CollatzResearch.WordTrace]
  refine ⟨29457415524025723060937677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39276554032034297414583569 29457415524025723060937677)
  ·
    refine ⟨11046530821509646147851629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29457415524025723060937677 11046530821509646147851629)
    ·
      refine ⟨4142449058066117305444361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11046530821509646147851629 4142449058066117305444361)
      ·
        refine ⟨3106836793549587979083271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4142449058066117305444361 3106836793549587979083271)
        ·
          refine ⟨4660255190324381968624907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3106836793549587979083271 4660255190324381968624907)
          ·
            refine ⟨6990382785486572952937361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4660255190324381968624907 6990382785486572952937361)
            ·
              refine ⟨5242787089114929714703021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6990382785486572952937361 5242787089114929714703021)
              ·
                refine ⟨1966045158418098643013633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5242787089114929714703021 1966045158418098643013633)
                ·
                  refine ⟨1474533868813573982260225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1966045158418098643013633 1474533868813573982260225)
                  ·
                    refine ⟨1105900401610180486695169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1474533868813573982260225 1105900401610180486695169)
                    ·
                      refine ⟨829425301207635365021377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1105900401610180486695169 829425301207635365021377)
                      ·
                        rfl

theorem cell23_1615300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_1615300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615300 prefixEnd_1615300 := by exact prefixLift 1615300
  have htrace : WordTrace (prefixWord ++ tailWord_1615300) baseStart_1615300 baseEnd_1615300 := by
    simpa [prefixWord, tailWord_1615300, baseEnd_1615300] using wordTrace_append hprefix tailTrace_1615300
  have hstable : (prefixWord ++ tailWord_1615300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615300).length < 2 ^ (prefixWord ++ tailWord_1615300).sum := by decide
  have hdescent : baseEnd_1615300 < baseStart_1615300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615332 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 1, 10]
def baseStart_1615332 : Nat := 118140960795 + 1615332 * 2 ^ 59
def prefixEnd_1615332 : Nat := 4983230072969 + 3 ^ 40 * 1615332 * 2
def baseEnd_1615332 : Nat := 276480577529526413273743

theorem tailTrace_1615332 : CollatzResearch.WordTrace tailWord_1615332 prefixEnd_1615332 276480577529526413273743 := by
  unfold tailWord_1615332
  simp only [CollatzResearch.WordTrace]
  refine ⟨29457999091967757793520125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39277332122623677058026833 29457999091967757793520125)
  ·
    refine ⟨11046749659487909172570047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29457999091967757793520125 11046749659487909172570047)
    ·
      refine ⟨16570124489231863758855071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11046749659487909172570047 16570124489231863758855071)
      ·
        refine ⟨24855186733847795638282607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16570124489231863758855071 24855186733847795638282607)
        ·
          refine ⟨37282780100771693457423911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24855186733847795638282607 37282780100771693457423911)
          ·
            refine ⟨55924170151157540186135867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37282780100771693457423911 55924170151157540186135867)
            ·
              refine ⟨83886255226736310279203801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55924170151157540186135867 83886255226736310279203801)
              ·
                refine ⟨62914691420052232709402851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83886255226736310279203801 62914691420052232709402851)
                ·
                  refine ⟨94372037130078349064104277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62914691420052232709402851 94372037130078349064104277)
                  ·
                    refine ⟨276480577529526413273743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 94372037130078349064104277 276480577529526413273743)
                    ·
                      rfl

theorem cell23_1615332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_1615332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615332 prefixEnd_1615332 := by exact prefixLift 1615332
  have htrace : WordTrace (prefixWord ++ tailWord_1615332) baseStart_1615332 baseEnd_1615332 := by
    simpa [prefixWord, tailWord_1615332, baseEnd_1615332] using wordTrace_append hprefix tailTrace_1615332
  have hstable : (prefixWord ++ tailWord_1615332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615332).length < 2 ^ (prefixWord ++ tailWord_1615332).sum := by decide
  have hdescent : baseEnd_1615332 < baseStart_1615332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615356 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 2, 4, 2]
def baseStart_1615356 : Nat := 118140960795 + 1615356 * 2 ^ 59
def prefixEnd_1615356 : Nat := 4983230072969 + 3 ^ 40 * 1615356 * 2
def baseEnd_1615356 : Nat := 829454056124287145921119

theorem tailTrace_1615356 : CollatzResearch.WordTrace tailWord_1615356 prefixEnd_1615356 829454056124287145921119 := by
  unfold tailWord_1615356
  simp only [CollatzResearch.WordTrace]
  refine ⟨29458436767924283842956961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39277915690565711790609281 29458436767924283842956961)
  ·
    refine ⟨22093827575943212882217721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29458436767924283842956961 22093827575943212882217721)
    ·
      refine ⟨16570370681957409661663291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22093827575943212882217721 16570370681957409661663291)
      ·
        refine ⟨24855556022936114492494937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16570370681957409661663291 24855556022936114492494937)
        ·
          refine ⟨18641667017202085869371203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24855556022936114492494937 18641667017202085869371203)
          ·
            refine ⟨27962500525803128804056805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18641667017202085869371203 27962500525803128804056805)
            ·
              refine ⟨5242968848588086650760651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27962500525803128804056805 5242968848588086650760651)
              ·
                refine ⟨7864453272882129976140977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5242968848588086650760651 7864453272882129976140977)
                ·
                  refine ⟨5898339954661597482105733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7864453272882129976140977 5898339954661597482105733)
                  ·
                    refine ⟨1105938741499049527894825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5898339954661597482105733 1105938741499049527894825)
                    ·
                      refine ⟨829454056124287145921119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1105938741499049527894825 829454056124287145921119)
                      ·
                        rfl

theorem cell23_1615356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_1615356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615356 prefixEnd_1615356 := by exact prefixLift 1615356
  have htrace : WordTrace (prefixWord ++ tailWord_1615356) baseStart_1615356 baseEnd_1615356 := by
    simpa [prefixWord, tailWord_1615356, baseEnd_1615356] using wordTrace_append hprefix tailTrace_1615356
  have hstable : (prefixWord ++ tailWord_1615356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615356).length < 2 ^ (prefixWord ++ tailWord_1615356).sum := by decide
  have hdescent : baseEnd_1615356 < baseStart_1615356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615359 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 3]
def baseStart_1615359 : Nat := 118140960795 + 1615359 * 2 ^ 59
def prefixEnd_1615359 : Nat := 4983230072969 + 3 ^ 40 * 1615359 * 2
def baseEnd_1615359 : Nat := 829455596566250634183605

theorem tailTrace_1615359 : CollatzResearch.WordTrace tailWord_1615359 prefixEnd_1615359 829455596566250634183605 := by
  unfold tailWord_1615359
  simp only [CollatzResearch.WordTrace]
  refine ⟨58916982954837699198273131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39277988636558466132182087 58916982954837699198273131)
  ·
    refine ⟨88375474432256548797409697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58916982954837699198273131 88375474432256548797409697)
    ·
      refine ⟨66281605824192411598057273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88375474432256548797409697 66281605824192411598057273)
      ·
        refine ⟨49711204368144308698542955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66281605824192411598057273 49711204368144308698542955)
        ·
          refine ⟨74566806552216463047814433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49711204368144308698542955 74566806552216463047814433)
          ·
            refine ⟨55925104914162347285860825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74566806552216463047814433 55925104914162347285860825)
            ·
              refine ⟨41943828685621760464395619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55925104914162347285860825 41943828685621760464395619)
              ·
                refine ⟨62915743028432640696593429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41943828685621760464395619 62915743028432640696593429)
                ·
                  refine ⟨2949175454457780032652817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62915743028432640696593429 2949175454457780032652817)
                  ·
                    refine ⟨2211881590843335024489613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2949175454457780032652817 2211881590843335024489613)
                    ·
                      refine ⟨829455596566250634183605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2211881590843335024489613 829455596566250634183605)
                      ·
                        rfl

theorem cell23_1615359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_1615359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615359 prefixEnd_1615359 := by exact prefixLift 1615359
  have htrace : WordTrace (prefixWord ++ tailWord_1615359) baseStart_1615359 baseEnd_1615359 := by
    simpa [prefixWord, tailWord_1615359, baseEnd_1615359] using wordTrace_append hprefix tailTrace_1615359
  have hstable : (prefixWord ++ tailWord_1615359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615359).length < 2 ^ (prefixWord ++ tailWord_1615359).sum := by decide
  have hdescent : baseEnd_1615359 < baseStart_1615359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615400 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 3, 4]
def baseStart_1615400 : Nat := 118140960795 + 1615400 * 2 ^ 59
def prefixEnd_1615400 : Nat := 4983230072969 + 3 ^ 40 * 1615400 * 2
def baseEnd_1615400 : Nat := 276492216424361657923639

theorem tailTrace_1615400 : CollatzResearch.WordTrace tailWord_1615400 prefixEnd_1615400 276492216424361657923639 := by
  unfold tailWord_1615400
  simp only [CollatzResearch.WordTrace]
  refine ⟨29459239173844581600257827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39278985565126108800343769 29459239173844581600257827)
  ·
    refine ⟨44188858760766872400386741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29459239173844581600257827 44188858760766872400386741)
    ·
      refine ⟨4142705508821894287536257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44188858760766872400386741 4142705508821894287536257)
      ·
        refine ⟨3107029131616420715652193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4142705508821894287536257 3107029131616420715652193)
        ·
          refine ⟨2330271848712315536739145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3107029131616420715652193 2330271848712315536739145)
          ·
            refine ⟨1747703886534236652554359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2330271848712315536739145 1747703886534236652554359)
            ·
              refine ⟨2621555829801354978831539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1747703886534236652554359 2621555829801354978831539)
              ·
                refine ⟨3932333744702032468247309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2621555829801354978831539 3932333744702032468247309)
                ·
                  refine ⟨1474625154263262175592741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3932333744702032468247309 1474625154263262175592741)
                  ·
                    refine ⟨276492216424361657923639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1474625154263262175592741 276492216424361657923639)
                    ·
                      rfl

theorem cell23_1615400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_1615400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615400 prefixEnd_1615400 := by exact prefixLift 1615400
  have htrace : WordTrace (prefixWord ++ tailWord_1615400) baseStart_1615400 baseEnd_1615400 := by
    simpa [prefixWord, tailWord_1615400, baseEnd_1615400] using wordTrace_append hprefix tailTrace_1615400
  have hstable : (prefixWord ++ tailWord_1615400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615400).length < 2 ^ (prefixWord ++ tailWord_1615400).sum := by decide
  have hdescent : baseEnd_1615400 < baseStart_1615400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615409 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 3, 5]
def baseStart_1615409 : Nat := 118140960795 + 1615409 * 2 ^ 59
def prefixEnd_1615409 : Nat := 4983230072969 + 3 ^ 40 * 1615409 * 2
def baseEnd_1615409 : Nat := 276493756866325146186125

theorem tailTrace_1615409 : CollatzResearch.WordTrace tailWord_1615409 prefixEnd_1615409 276493756866325146186125 := by
  unfold tailWord_1615409
  simp only [CollatzResearch.WordTrace]
  refine ⟨58918806604656557737593281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39279204403104371825062187 58918806604656557737593281)
  ·
    refine ⟨44189104953492418303194961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58918806604656557737593281 44189104953492418303194961)
    ·
      refine ⟨33141828715119313727396221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44189104953492418303194961 33141828715119313727396221)
      ·
        refine ⟨12428185768169742647773583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33141828715119313727396221 12428185768169742647773583)
        ·
          refine ⟨18642278652254613971660375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12428185768169742647773583 18642278652254613971660375)
          ·
            refine ⟨27963417978381920957490563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18642278652254613971660375 27963417978381920957490563)
            ·
              refine ⟨41945126967572881436235845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27963417978381920957490563 41945126967572881436235845)
              ·
                refine ⟨7864711306419915269294221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41945126967572881436235845 7864711306419915269294221)
                ·
                  refine ⟨2949266739907468225985333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7864711306419915269294221 2949266739907468225985333)
                  ·
                    refine ⟨276493756866325146186125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2949266739907468225985333 276493756866325146186125)
                    ·
                      rfl

theorem cell23_1615409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_1615409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615409 prefixEnd_1615409 := by exact prefixLift 1615409
  have htrace : WordTrace (prefixWord ++ tailWord_1615409) baseStart_1615409 baseEnd_1615409 := by
    simpa [prefixWord, tailWord_1615409, baseEnd_1615409] using wordTrace_append hprefix tailTrace_1615409
  have hstable : (prefixWord ++ tailWord_1615409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615409).length < 2 ^ (prefixWord ++ tailWord_1615409).sum := by decide
  have hdescent : baseEnd_1615409 < baseStart_1615409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615413 : List Nat := [1, 3, 3, 1, 1, 5, 2, 1, 6]
def baseStart_1615413 : Nat := 118140960795 + 1615413 * 2 ^ 59
def prefixEnd_1615413 : Nat := 4983230072969 + 3 ^ 40 * 1615413 * 2
def baseEnd_1615413 : Nat := 92164813835732602545373

theorem tailTrace_1615413 : CollatzResearch.WordTrace tailWord_1615413 prefixEnd_1615413 92164813835732602545373 := by
  unfold tailWord_1615413
  simp only [CollatzResearch.WordTrace]
  refine ⟨58918952496642066420738893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39279301664428044280492595 58918952496642066420738893)
  ·
    refine ⟨22094607186240774907777085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58918952496642066420738893 22094607186240774907777085)
    ·
      refine ⟨8285477694840290590416407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22094607186240774907777085 8285477694840290590416407)
      ·
        refine ⟨12428216542260435885624611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8285477694840290590416407 12428216542260435885624611)
        ·
          refine ⟨18642324813390653828436917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12428216542260435885624611 18642324813390653828436917)
          ·
            refine ⟨1747717951255373796415961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18642324813390653828436917 1747717951255373796415961)
            ·
              refine ⟨1310788463441530347311971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1747717951255373796415961 1310788463441530347311971)
              ·
                refine ⟨1966182695162295520967957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1310788463441530347311971 1966182695162295520967957)
                ·
                  refine ⟨92164813835732602545373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1966182695162295520967957 92164813835732602545373)
                  ·
                    rfl

theorem cell23_1615413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 6].length) (baseStart_1615413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615413 prefixEnd_1615413 := by exact prefixLift 1615413
  have htrace : WordTrace (prefixWord ++ tailWord_1615413) baseStart_1615413 baseEnd_1615413 := by
    simpa [prefixWord, tailWord_1615413, baseEnd_1615413] using wordTrace_append hprefix tailTrace_1615413
  have hstable : (prefixWord ++ tailWord_1615413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615413).length < 2 ^ (prefixWord ++ tailWord_1615413).sum := by decide
  have hdescent : baseEnd_1615413 < baseStart_1615413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615513 : List Nat := [1, 2, 1, 2, 1, 2, 2, 6, 2, 1, 3]
def baseStart_1615513 : Nat := 118140960795 + 1615513 * 2 ^ 59
def prefixEnd_1615513 : Nat := 4983230072969 + 3 ^ 40 * 1615513 * 2
def baseEnd_1615513 : Nat := 829534672587043031657897

theorem tailTrace_1615513 : CollatzResearch.WordTrace tailWord_1615513 prefixEnd_1615513 829534672587043031657897 := by
  unfold tailWord_1615513
  simp only [CollatzResearch.WordTrace]
  refine ⟨58922599796279783499379193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39281733197519855666252795 58922599796279783499379193)
  ·
    refine ⟨44191949847209837624534395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58922599796279783499379193 44191949847209837624534395)
    ·
      refine ⟨66287924770814756436801593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44191949847209837624534395 66287924770814756436801593)
      ·
        refine ⟨49715943578111067327601195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66287924770814756436801593 49715943578111067327601195)
        ·
          refine ⟨74573915367166600991401793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49715943578111067327601195 74573915367166600991401793)
          ·
            refine ⟨55930436525374950743551345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74573915367166600991401793 55930436525374950743551345)
            ·
              refine ⟨41947827394031213057663509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55930436525374950743551345 41947827394031213057663509)
              ·
                refine ⟨1966304409095213112077977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41947827394031213057663509 1966304409095213112077977)
                ·
                  refine ⟨1474728306821409834058483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1966304409095213112077977 1474728306821409834058483)
                  ·
                    refine ⟨2212092460232114751087725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1474728306821409834058483 2212092460232114751087725)
                    ·
                      refine ⟨829534672587043031657897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2212092460232114751087725 829534672587043031657897)
                      ·
                        rfl

theorem cell23_1615513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 1, 3].length) (baseStart_1615513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615513 prefixEnd_1615513 := by exact prefixLift 1615513
  have htrace : WordTrace (prefixWord ++ tailWord_1615513) baseStart_1615513 baseEnd_1615513 := by
    simpa [prefixWord, tailWord_1615513, baseEnd_1615513] using wordTrace_append hprefix tailTrace_1615513
  have hstable : (prefixWord ++ tailWord_1615513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615513).length < 2 ^ (prefixWord ++ tailWord_1615513).sum := by decide
  have hdescent : baseEnd_1615513 < baseStart_1615513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615529 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 6, 6]
def baseStart_1615529 : Nat := 118140960795 + 1615529 * 2 ^ 59
def prefixEnd_1615529 : Nat := 4983230072969 + 3 ^ 40 * 1615529 * 2
def baseEnd_1615529 : Nat := 276514296092504989685941

theorem tailTrace_1615529 : CollatzResearch.WordTrace tailWord_1615529 prefixEnd_1615529 276514296092504989685941 := by
  unfold tailWord_1615529
  simp only [CollatzResearch.WordTrace]
  refine ⟨58923183364221818231961641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39282122242814545487974427 58923183364221818231961641)
  ·
    refine ⟨44192387523166363673971231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58923183364221818231961641 44192387523166363673971231)
    ·
      refine ⟨66288581284749545510956847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44192387523166363673971231 66288581284749545510956847)
      ·
        refine ⟨99432871927124318266435271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66288581284749545510956847 99432871927124318266435271)
        ·
          refine ⟨149149307890686477399652907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99432871927124318266435271 149149307890686477399652907)
          ·
            refine ⟨223723961836029716099479361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149149307890686477399652907 223723961836029716099479361)
            ·
              refine ⟨167792971377022287074609521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223723961836029716099479361 167792971377022287074609521)
              ·
                refine ⟨125844728532766715305957141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167792971377022287074609521 125844728532766715305957141)
                ·
                  refine ⟨5898971649973439779966741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125844728532766715305957141 5898971649973439779966741)
                  ·
                    refine ⟨276514296092504989685941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5898971649973439779966741 276514296092504989685941)
                    ·
                      rfl

theorem cell23_1615529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 6].length) (baseStart_1615529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615529 prefixEnd_1615529 := by exact prefixLift 1615529
  have htrace : WordTrace (prefixWord ++ tailWord_1615529) baseStart_1615529 baseEnd_1615529 := by
    simpa [prefixWord, tailWord_1615529, baseEnd_1615529] using wordTrace_append hprefix tailTrace_1615529
  have hstable : (prefixWord ++ tailWord_1615529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615529).length < 2 ^ (prefixWord ++ tailWord_1615529).sum := by decide
  have hdescent : baseEnd_1615529 < baseStart_1615529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615581 : List Nat := [1, 4, 3, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_1615581 : Nat := 118140960795 + 1615581 * 2 ^ 59
def prefixEnd_1615581 : Nat := 4983230072969 + 3 ^ 40 * 1615581 * 2
def baseEnd_1615581 : Nat := 829569589271548765607585

theorem tailTrace_1615581 : CollatzResearch.WordTrace tailWord_1615581 prefixEnd_1615581 829569589271548765607585 := by
  unfold tailWord_1615581
  simp only [CollatzResearch.WordTrace]
  refine ⟨58925079960033431112854597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39283386640022287408569731 58925079960033431112854597)
  ·
    refine ⟨11048452492506268333660237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58925079960033431112854597 11048452492506268333660237)
    ·
      refine ⟨4143169684689850625122589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11048452492506268333660237 4143169684689850625122589)
      ·
        refine ⟨1553688631758693984420971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4143169684689850625122589 1553688631758693984420971)
        ·
          refine ⟨2330532947638040976631457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1553688631758693984420971 2330532947638040976631457)
          ·
            refine ⟨1747899710728530732473593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2330532947638040976631457 1747899710728530732473593)
            ·
              refine ⟨1310924783046398049355195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1747899710728530732473593 1310924783046398049355195)
              ·
                refine ⟨1966387174569597074032793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1310924783046398049355195 1966387174569597074032793)
                ·
                  refine ⟨1474790380927197805524595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1966387174569597074032793 1474790380927197805524595)
                  ·
                    refine ⟨2212185571390796708286893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1474790380927197805524595 2212185571390796708286893)
                    ·
                      refine ⟨829569589271548765607585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2212185571390796708286893 829569589271548765607585)
                      ·
                        rfl

theorem cell23_1615581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_1615581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615581 prefixEnd_1615581 := by exact prefixLift 1615581
  have htrace : WordTrace (prefixWord ++ tailWord_1615581) baseStart_1615581 baseEnd_1615581 := by
    simpa [prefixWord, tailWord_1615581, baseEnd_1615581] using wordTrace_append hprefix tailTrace_1615581
  have hstable : (prefixWord ++ tailWord_1615581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615581).length < 2 ^ (prefixWord ++ tailWord_1615581).sum := by decide
  have hdescent : baseEnd_1615581 < baseStart_1615581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615591 : List Nat := [1, 1, 5, 4, 2, 1, 1, 2, 1, 3, 2]
def baseStart_1615591 : Nat := 118140960795 + 1615591 * 2 ^ 59
def prefixEnd_1615591 : Nat := 4983230072969 + 3 ^ 40 * 1615591 * 2
def baseEnd_1615591 : Nat := 829574724078093726482539

theorem tailTrace_1615591 : CollatzResearch.WordTrace tailWord_1615591 prefixEnd_1615591 829574724078093726482539 := by
  unfold tailWord_1615591
  simp only [CollatzResearch.WordTrace]
  refine ⟨58925444689997202820718627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39283629793331468547145751 58925444689997202820718627)
  ·
    refine ⟨88388167034995804231077941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58925444689997202820718627 88388167034995804231077941)
    ·
      refine ⟨8286390659530856646663557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88388167034995804231077941 8286390659530856646663557)
      ·
        refine ⟨1553698248662035621249417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8286390659530856646663557 1553698248662035621249417)
        ·
          refine ⟨1165273686496526715937063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1553698248662035621249417 1165273686496526715937063)
          ·
            refine ⟨1747910529744790073905595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165273686496526715937063 1747910529744790073905595)
            ·
              refine ⟨2621865794617185110858393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1747910529744790073905595 2621865794617185110858393)
              ·
                refine ⟨1966399345962888833143795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2621865794617185110858393 1966399345962888833143795)
                ·
                  refine ⟨2949599018944333249715693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966399345962888833143795 2949599018944333249715693)
                  ·
                    refine ⟨1106099632104124968643385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2949599018944333249715693 1106099632104124968643385)
                    ·
                      refine ⟨829574724078093726482539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1106099632104124968643385 829574724078093726482539)
                      ·
                        rfl

theorem cell23_1615591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_1615591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615591 prefixEnd_1615591 := by exact prefixLift 1615591
  have htrace : WordTrace (prefixWord ++ tailWord_1615591) baseStart_1615591 baseEnd_1615591 := by
    simpa [prefixWord, tailWord_1615591, baseEnd_1615591] using wordTrace_append hprefix tailTrace_1615591
  have hstable : (prefixWord ++ tailWord_1615591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615591).length < 2 ^ (prefixWord ++ tailWord_1615591).sum := by decide
  have hdescent : baseEnd_1615591 < baseStart_1615591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615604 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_1615604 : Nat := 118140960795 + 1615604 * 2 ^ 59
def prefixEnd_1615604 : Nat := 4983230072969 + 3 ^ 40 * 1615604 * 2
def baseEnd_1615604 : Nat := 829581399326602175619979

theorem tailTrace_1615604 : CollatzResearch.WordTrace tailWord_1615604 prefixEnd_1615604 829581399326602175619979 := by
  unfold tailWord_1615604
  simp only [CollatzResearch.WordTrace]
  refine ⟨29462959419475053020470933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39283945892633404027294577 29462959419475053020470933)
  ·
    refine ⟨1381076222787893110334575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29462959419475053020470933 1381076222787893110334575)
    ·
      refine ⟨2071614334181839665501863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1381076222787893110334575 2071614334181839665501863)
      ·
        refine ⟨3107421501272759498252795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2071614334181839665501863 3107421501272759498252795)
        ·
          refine ⟨4661132251909139247379193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3107421501272759498252795 4661132251909139247379193)
          ·
            refine ⟨3495849188931854435534395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4661132251909139247379193 3495849188931854435534395)
            ·
              refine ⟨5243773783397781653301593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3495849188931854435534395 5243773783397781653301593)
              ·
                refine ⟨3932830337548336239976195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5243773783397781653301593 3932830337548336239976195)
                ·
                  refine ⟨5899245506322504359964293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3932830337548336239976195 5899245506322504359964293)
                  ·
                    refine ⟨1106108532435469567493305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5899245506322504359964293 1106108532435469567493305)
                    ·
                      refine ⟨829581399326602175619979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1106108532435469567493305 829581399326602175619979)
                      ·
                        rfl

theorem cell23_1615604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_1615604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615604 prefixEnd_1615604 := by exact prefixLift 1615604
  have htrace : WordTrace (prefixWord ++ tailWord_1615604) baseStart_1615604 baseEnd_1615604 := by
    simpa [prefixWord, tailWord_1615604, baseEnd_1615604] using wordTrace_append hprefix tailTrace_1615604
  have hstable : (prefixWord ++ tailWord_1615604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615604).length < 2 ^ (prefixWord ++ tailWord_1615604).sum := by decide
  have hdescent : baseEnd_1615604 < baseStart_1615604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615643 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 2, 4, 2]
def baseStart_1615643 : Nat := 118140960795 + 1615643 * 2 ^ 59
def prefixEnd_1615643 : Nat := 4983230072969 + 3 ^ 40 * 1615643 * 2
def baseEnd_1615643 : Nat := 829601425072127523032299

theorem tailTrace_1615643 : CollatzResearch.WordTrace tailWord_1615643 prefixEnd_1615643 829601425072127523032299 := by
  unfold tailWord_1615643
  simp only [CollatzResearch.WordTrace]
  refine ⟨58927341285808815701611583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39284894190539210467741055 58927341285808815701611583)
  ·
    refine ⟨88391011928713223552417375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58927341285808815701611583 88391011928713223552417375)
    ·
      refine ⟨132586517893069835328626063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88391011928713223552417375 132586517893069835328626063)
      ·
        refine ⟨198879776839604752992939095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132586517893069835328626063 198879776839604752992939095)
        ·
          refine ⟨298319665259407129489408643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198879776839604752992939095 298319665259407129489408643)
          ·
            refine ⟨447479497889110694234112965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298319665259407129489408643 447479497889110694234112965)
            ·
              refine ⟨83902405854208255168896181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 447479497889110694234112965 83902405854208255168896181)
              ·
                refine ⟨7865850548832023922084017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83902405854208255168896181 7865850548832023922084017)
                ·
                  refine ⟨5899387911624017941563013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7865850548832023922084017 5899387911624017941563013)
                  ·
                    refine ⟨1106135233429503364043065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5899387911624017941563013 1106135233429503364043065)
                    ·
                      refine ⟨829601425072127523032299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1106135233429503364043065 829601425072127523032299)
                      ·
                        rfl

theorem cell23_1615643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 4, 2].length) (baseStart_1615643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615643 prefixEnd_1615643 := by exact prefixLift 1615643
  have htrace : WordTrace (prefixWord ++ tailWord_1615643) baseStart_1615643 baseEnd_1615643 := by
    simpa [prefixWord, tailWord_1615643, baseEnd_1615643] using wordTrace_append hprefix tailTrace_1615643
  have hstable : (prefixWord ++ tailWord_1615643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615643).length < 2 ^ (prefixWord ++ tailWord_1615643).sum := by decide
  have hdescent : baseEnd_1615643 < baseStart_1615643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615653 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 5, 4]
def baseStart_1615653 : Nat := 118140960795 + 1615653 * 2 ^ 59
def prefixEnd_1615653 : Nat := 4983230072969 + 3 ^ 40 * 1615653 * 2
def baseEnd_1615653 : Nat := 276535519959557494635751

theorem tailTrace_1615653 : CollatzResearch.WordTrace tailWord_1615653 prefixEnd_1615653 276535519959557494635751 := by
  unfold tailWord_1615653
  simp only [CollatzResearch.WordTrace]
  refine ⟨58927706015772587409475613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39285137343848391606317075 58927706015772587409475613)
  ·
    refine ⟨22097889755914720278553355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58927706015772587409475613 22097889755914720278553355)
    ·
      refine ⟨33146834633872080417830033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22097889755914720278553355 33146834633872080417830033)
      ·
        refine ⟨24860125975404060313372525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33146834633872080417830033 24860125975404060313372525)
        ·
          refine ⟨9322547240776522617514697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24860125975404060313372525 9322547240776522617514697)
          ·
            refine ⟨6991910430582391963136023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9322547240776522617514697 6991910430582391963136023)
            ·
              refine ⟨10487865645873587944704035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6991910430582391963136023 10487865645873587944704035)
              ·
                refine ⟨15731798468810381917056053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10487865645873587944704035 15731798468810381917056053)
                ·
                  refine ⟨1474856106450973304724005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15731798468810381917056053 1474856106450973304724005)
                  ·
                    refine ⟨276535519959557494635751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1474856106450973304724005 276535519959557494635751)
                    ·
                      rfl

theorem cell23_1615653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_1615653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615653 prefixEnd_1615653 := by exact prefixLift 1615653
  have htrace : WordTrace (prefixWord ++ tailWord_1615653) baseStart_1615653 baseEnd_1615653 := by
    simpa [prefixWord, tailWord_1615653, baseEnd_1615653] using wordTrace_append hprefix tailTrace_1615653
  have hstable : (prefixWord ++ tailWord_1615653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615653).length < 2 ^ (prefixWord ++ tailWord_1615653).sum := by decide
  have hdescent : baseEnd_1615653 < baseStart_1615653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615660 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 4]
def baseStart_1615660 : Nat := 118140960795 + 1615660 * 2 ^ 59
def prefixEnd_1615660 : Nat := 4983230072969 + 3 ^ 40 * 1615660 * 2
def baseEnd_1615660 : Nat := 829610154243253956519721

theorem tailTrace_1615660 : CollatzResearch.WordTrace tailWord_1615660 prefixEnd_1615660 829610154243253956519721 := by
  unfold tailWord_1615660
  simp only [CollatzResearch.WordTrace]
  refine ⟨29463980663373613802490217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39285307551164818403320289 29463980663373613802490217)
  ·
    refine ⟨22097985497530210351867663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29463980663373613802490217 22097985497530210351867663)
    ·
      refine ⟨33146978246295315527801495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22097985497530210351867663 33146978246295315527801495)
      ·
        refine ⟨49720467369442973291702243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33146978246295315527801495 49720467369442973291702243)
        ·
          refine ⟨74580701054164459937553365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49720467369442973291702243 74580701054164459937553365)
          ·
            refine ⟨1747985180956979529786407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 74580701054164459937553365 1747985180956979529786407)
            ·
              refine ⟨2621977771435469294679611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1747985180956979529786407 2621977771435469294679611)
              ·
                refine ⟨3932966657153203942019417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2621977771435469294679611 3932966657153203942019417)
                ·
                  refine ⟨2949724992864902956514563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3932966657153203942019417 2949724992864902956514563)
                  ·
                    refine ⟨4424587489297354434771845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2949724992864902956514563 4424587489297354434771845)
                    ·
                      refine ⟨829610154243253956519721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4424587489297354434771845 829610154243253956519721)
                      ·
                        rfl

theorem cell23_1615660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_1615660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615660 prefixEnd_1615660 := by exact prefixLift 1615660
  have htrace : WordTrace (prefixWord ++ tailWord_1615660) baseStart_1615660 baseEnd_1615660 := by
    simpa [prefixWord, tailWord_1615660, baseEnd_1615660] using wordTrace_append hprefix tailTrace_1615660
  have hstable : (prefixWord ++ tailWord_1615660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615660).length < 2 ^ (prefixWord ++ tailWord_1615660).sum := by decide
  have hdescent : baseEnd_1615660 < baseStart_1615660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615683 : List Nat := [1, 1, 1, 3, 1, 5, 3, 2, 6]
def baseStart_1615683 : Nat := 118140960795 + 1615683 * 2 ^ 59
def prefixEnd_1615683 : Nat := 4983230072969 + 3 ^ 40 * 1615683 * 2
def baseEnd_1615683 : Nat := 92180218255367485170235

theorem tailTrace_1615683 : CollatzResearch.WordTrace tailWord_1615683 prefixEnd_1615683 92180218255367485170235 := by
  unfold tailWord_1615683
  simp only [CollatzResearch.WordTrace]
  refine ⟨58928800205663902533067703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39285866803775935022045135 58928800205663902533067703)
  ·
    refine ⟨88393200308495853799601555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58928800205663902533067703 88393200308495853799601555)
    ·
      refine ⟨132589800462743780699402333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88393200308495853799601555 132589800462743780699402333)
      ·
        refine ⟨49721175173528917762275875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132589800462743780699402333 49721175173528917762275875)
        ·
          refine ⟨74581762760293376643413813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49721175173528917762275875 74581762760293376643413813)
          ·
            refine ⟨6992040258777504060320045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74581762760293376643413813 6992040258777504060320045)
            ·
              refine ⟨2622015097041564022620017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6992040258777504060320045 2622015097041564022620017)
              ·
                refine ⟨1966511322781173016965013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2622015097041564022620017 1966511322781173016965013)
                ·
                  refine ⟨92180218255367485170235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1966511322781173016965013 92180218255367485170235)
                  ·
                    rfl

theorem cell23_1615683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 6].length) (baseStart_1615683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615683 prefixEnd_1615683 := by exact prefixLift 1615683
  have htrace : WordTrace (prefixWord ++ tailWord_1615683) baseStart_1615683 baseEnd_1615683 := by
    simpa [prefixWord, tailWord_1615683, baseEnd_1615683] using wordTrace_append hprefix tailTrace_1615683
  have hstable : (prefixWord ++ tailWord_1615683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615683).length < 2 ^ (prefixWord ++ tailWord_1615683).sum := by decide
  have hdescent : baseEnd_1615683 < baseStart_1615683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615720 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 1, 5, 2]
def baseStart_1615720 : Nat := 118140960795 + 1615720 * 2 ^ 59
def prefixEnd_1615720 : Nat := 4983230072969 + 3 ^ 40 * 1615720 * 2
def baseEnd_1615720 : Nat := 829640963082523721769445

theorem tailTrace_1615720 : CollatzResearch.WordTrace tailWord_1615720 prefixEnd_1615720 829640963082523721769445 := by
  unfold tailWord_1615720
  simp only [CollatzResearch.WordTrace]
  refine ⟨29465074853264928926082307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39286766471019905234776409 29465074853264928926082307)
  ·
    refine ⟨44197612279897393389123461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29465074853264928926082307 44197612279897393389123461)
    ·
      refine ⟨8287052302480761260460649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44197612279897393389123461 8287052302480761260460649)
      ·
        refine ⟨6215289226860570945345487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8287052302480761260460649 6215289226860570945345487)
        ·
          refine ⟨9322933840290856418018231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6215289226860570945345487 9322933840290856418018231)
          ·
            refine ⟨13984400760436284627027347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9322933840290856418018231 13984400760436284627027347)
            ·
              refine ⟨20976601140654426940541021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13984400760436284627027347 20976601140654426940541021)
              ·
                refine ⟨7866225427745410102702883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20976601140654426940541021 7866225427745410102702883)
                ·
                  refine ⟨11799338141618115154054325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7866225427745410102702883 11799338141618115154054325)
                  ·
                    refine ⟨1106187950776698295692593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11799338141618115154054325 1106187950776698295692593)
                    ·
                      refine ⟨829640963082523721769445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1106187950776698295692593 829640963082523721769445)
                      ·
                        rfl

theorem cell23_1615720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_1615720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615720 prefixEnd_1615720 := by exact prefixLift 1615720
  have htrace : WordTrace (prefixWord ++ tailWord_1615720) baseStart_1615720 baseEnd_1615720 := by
    simpa [prefixWord, tailWord_1615720, baseEnd_1615720] using wordTrace_append hprefix tailTrace_1615720
  have hstable : (prefixWord ++ tailWord_1615720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615720).length < 2 ^ (prefixWord ++ tailWord_1615720).sum := by decide
  have hdescent : baseEnd_1615720 < baseStart_1615720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615744 : List Nat := [2, 1, 1, 2, 1, 2, 7, 2, 1, 1, 3]
def baseStart_1615744 : Nat := 118140960795 + 1615744 * 2 ^ 59
def prefixEnd_1615744 : Nat := 4983230072969 + 3 ^ 40 * 1615744 * 2
def baseEnd_1615744 : Nat := 829653286618231627869335

theorem tailTrace_1615744 : CollatzResearch.WordTrace tailWord_1615744 prefixEnd_1615744 829653286618231627869335 := by
  unfold tailWord_1615744
  simp only [CollatzResearch.WordTrace]
  refine ⟨29465512529221454975519143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39287350038961939967358857 29465512529221454975519143)
  ·
    refine ⟨44198268793832182463278715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29465512529221454975519143 44198268793832182463278715)
    ·
      refine ⟨66297403190748273694918073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44198268793832182463278715 66297403190748273694918073)
      ·
        refine ⟨49723052393061205271188555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66297403190748273694918073 49723052393061205271188555)
        ·
          refine ⟨74584578589591807906782833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49723052393061205271188555 74584578589591807906782833)
          ·
            refine ⟨55938433942193855930087125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74584578589591807906782833 55938433942193855930087125)
            ·
              refine ⟨1311057045520168498361417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 55938433942193855930087125 1311057045520168498361417)
              ·
                refine ⟨983292784140126373771063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1311057045520168498361417 983292784140126373771063)
                ·
                  refine ⟨1474939176210189560656595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 983292784140126373771063 1474939176210189560656595)
                  ·
                    refine ⟨2212408764315284340984893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1474939176210189560656595 2212408764315284340984893)
                    ·
                      refine ⟨829653286618231627869335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2212408764315284340984893 829653286618231627869335)
                      ·
                        rfl

theorem cell23_1615744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 1, 1, 3].length) (baseStart_1615744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615744 prefixEnd_1615744 := by exact prefixLift 1615744
  have htrace : WordTrace (prefixWord ++ tailWord_1615744) baseStart_1615744 baseEnd_1615744 := by
    simpa [prefixWord, tailWord_1615744, baseEnd_1615744] using wordTrace_append hprefix tailTrace_1615744
  have hstable : (prefixWord ++ tailWord_1615744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615744).length < 2 ^ (prefixWord ++ tailWord_1615744).sum := by decide
  have hdescent : baseEnd_1615744 < baseStart_1615744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615753 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 1, 1, 5]
def baseStart_1615753 : Nat := 118140960795 + 1615753 * 2 ^ 59
def prefixEnd_1615753 : Nat := 4983230072969 + 3 ^ 40 * 1615753 * 2
def baseEnd_1615753 : Nat := 829657907944122092656793

theorem tailTrace_1615753 : CollatzResearch.WordTrace tailWord_1615753 prefixEnd_1615753 829657907944122092656793 := by
  unfold tailWord_1615753
  simp only [CollatzResearch.WordTrace]
  refine ⟨58931353315410304488115913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39287568876940202992077275 58931353315410304488115913)
  ·
    refine ⟨44198514986557728366086935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58931353315410304488115913 44198514986557728366086935)
    ·
      refine ⟨66297772479836592549130403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44198514986557728366086935 66297772479836592549130403)
      ·
        refine ⟨99446658719754888823695605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66297772479836592549130403 99446658719754888823695605)
        ·
          refine ⟨9323124254977020827221463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99446658719754888823695605 9323124254977020827221463)
          ·
            refine ⟨13984686382465531240832195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9323124254977020827221463 13984686382465531240832195)
            ·
              refine ⟨20977029573698296861248293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13984686382465531240832195 20977029573698296861248293)
              ·
                refine ⟨3933193045068430661484055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20977029573698296861248293 3933193045068430661484055)
                ·
                  refine ⟨5899789567602645992226083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3933193045068430661484055 5899789567602645992226083)
                  ·
                    refine ⟨8849684351403968988339125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5899789567602645992226083 8849684351403968988339125)
                    ·
                      refine ⟨829657907944122092656793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8849684351403968988339125 829657907944122092656793)
                      ·
                        rfl

theorem cell23_1615753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 1, 5].length) (baseStart_1615753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615753 prefixEnd_1615753 := by exact prefixLift 1615753
  have htrace : WordTrace (prefixWord ++ tailWord_1615753) baseStart_1615753 baseEnd_1615753 := by
    simpa [prefixWord, tailWord_1615753, baseEnd_1615753] using wordTrace_append hprefix tailTrace_1615753
  have hstable : (prefixWord ++ tailWord_1615753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615753).length < 2 ^ (prefixWord ++ tailWord_1615753).sum := by decide
  have hdescent : baseEnd_1615753 < baseStart_1615753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615767 : List Nat := [1, 1, 3, 3, 1, 5, 1, 2, 1, 1, 4]
def baseStart_1615767 : Nat := 118140960795 + 1615767 * 2 ^ 59
def prefixEnd_1615767 : Nat := 4983230072969 + 3 ^ 40 * 1615767 * 2
def baseEnd_1615767 : Nat := 829665096673285037881729

theorem tailTrace_1615767 : CollatzResearch.WordTrace tailWord_1615767 prefixEnd_1615767 829665096673285037881729 := by
  unfold tailWord_1615767
  simp only [CollatzResearch.WordTrace]
  refine ⟨58931863937359584879125555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39287909291573056586083703 58931863937359584879125555)
  ·
    refine ⟨88397795906039377318688333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58931863937359584879125555 88397795906039377318688333)
    ·
      refine ⟨33149173464764766494508125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88397795906039377318688333 33149173464764766494508125)
      ·
        refine ⟨12430940049286787435440547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33149173464764766494508125 12430940049286787435440547)
        ·
          refine ⟨18646410073930181153160821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12430940049286787435440547 18646410073930181153160821)
          ·
            refine ⟨1748100944430954483108827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18646410073930181153160821 1748100944430954483108827)
            ·
              refine ⟨2622151416646431724663241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748100944430954483108827 2622151416646431724663241)
              ·
                refine ⟨1966613562484823793497431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2622151416646431724663241 1966613562484823793497431)
                ·
                  refine ⟨2949920343727235690246147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966613562484823793497431 2949920343727235690246147)
                  ·
                    refine ⟨4424880515590853535369221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2949920343727235690246147 4424880515590853535369221)
                    ·
                      refine ⟨829665096673285037881729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4424880515590853535369221 829665096673285037881729)
                      ·
                        rfl

theorem cell23_1615767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_1615767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615767 prefixEnd_1615767 := by exact prefixLift 1615767
  have htrace : WordTrace (prefixWord ++ tailWord_1615767) baseStart_1615767 baseEnd_1615767 := by
    simpa [prefixWord, tailWord_1615767, baseEnd_1615767] using wordTrace_append hprefix tailTrace_1615767
  have hstable : (prefixWord ++ tailWord_1615767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615767).length < 2 ^ (prefixWord ++ tailWord_1615767).sum := by decide
  have hdescent : baseEnd_1615767 < baseStart_1615767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615773 : List Nat := [1, 4, 2, 1, 2, 2, 2, 9]
def baseStart_1615773 : Nat := 118140960795 + 1615773 * 2 ^ 59
def prefixEnd_1615773 : Nat := 4983230072969 + 3 ^ 40 * 1615773 * 2
def baseEnd_1615773 : Nat := 30728451020637482015063

theorem tailTrace_1615773 : CollatzResearch.WordTrace tailWord_1615773 prefixEnd_1615773 30728451020637482015063 := by
  unfold tailWord_1615773
  simp only [CollatzResearch.WordTrace]
  refine ⟨58932082775337847903843973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39288055183558565269229315 58932082775337847903843973)
  ·
    refine ⟨11049765520375846481970745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58932082775337847903843973 11049765520375846481970745)
    ·
      refine ⟨8287324140281884861478059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11049765520375846481970745 8287324140281884861478059)
      ·
        refine ⟨12430986210422827292217089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8287324140281884861478059 12430986210422827292217089)
        ·
          refine ⟨9323239657817120469162817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12430986210422827292217089 9323239657817120469162817)
          ·
            refine ⟨6992429743362840351872113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9323239657817120469162817 6992429743362840351872113)
            ·
              refine ⟨5244322307522130263904085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6992429743362840351872113 5244322307522130263904085)
              ·
                refine ⟨30728451020637482015063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5244322307522130263904085 30728451020637482015063)
                ·
                  rfl

theorem cell23_1615773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 9].length) (baseStart_1615773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615773 prefixEnd_1615773 := by exact prefixLift 1615773
  have htrace : WordTrace (prefixWord ++ tailWord_1615773) baseStart_1615773 baseEnd_1615773 := by
    simpa [prefixWord, tailWord_1615773, baseEnd_1615773] using wordTrace_append hprefix tailTrace_1615773
  have hstable : (prefixWord ++ tailWord_1615773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615773).length < 2 ^ (prefixWord ++ tailWord_1615773).sum := by decide
  have hdescent : baseEnd_1615773 < baseStart_1615773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615780 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_1615780 : Nat := 118140960795 + 1615780 * 2 ^ 59
def prefixEnd_1615780 : Nat := 4983230072969 + 3 ^ 40 * 1615780 * 2
def baseEnd_1615780 : Nat := 829671771921793487019169

theorem tailTrace_1615780 : CollatzResearch.WordTrace tailWord_1615780 prefixEnd_1615780 829671771921793487019169 := by
  unfold tailWord_1615780
  simp only [CollatzResearch.WordTrace]
  refine ⟨29466169043156244049674397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39288225390874992066232529 29466169043156244049674397)
  ·
    refine ⟨11049813391183591518627899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29466169043156244049674397 11049813391183591518627899)
    ·
      refine ⟨16574720086775387277941849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11049813391183591518627899 16574720086775387277941849)
      ·
        refine ⟨12431040065081540458456387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16574720086775387277941849 12431040065081540458456387)
        ·
          refine ⟨18646560097622310687684581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12431040065081540458456387 18646560097622310687684581)
          ·
            refine ⟨3496230018304183253940859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18646560097622310687684581 3496230018304183253940859)
            ·
              refine ⟨5244345027456274880911289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3496230018304183253940859 5244345027456274880911289)
              ·
                refine ⟨3933258770592206160683467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5244345027456274880911289 3933258770592206160683467)
                ·
                  refine ⟨5899888155888309241025201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3933258770592206160683467 5899888155888309241025201)
                  ·
                    refine ⟨4424916116916231930768901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5899888155888309241025201 4424916116916231930768901)
                    ·
                      refine ⟨829671771921793487019169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4424916116916231930768901 829671771921793487019169)
                      ·
                        rfl

theorem cell23_1615780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_1615780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615780 prefixEnd_1615780 := by exact prefixLift 1615780
  have htrace : WordTrace (prefixWord ++ tailWord_1615780) baseStart_1615780 baseEnd_1615780 := by
    simpa [prefixWord, tailWord_1615780, baseEnd_1615780] using wordTrace_append hprefix tailTrace_1615780
  have hstable : (prefixWord ++ tailWord_1615780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615780).length < 2 ^ (prefixWord ++ tailWord_1615780).sum := by decide
  have hdescent : baseEnd_1615780 < baseStart_1615780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615823 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 4]
def baseStart_1615823 : Nat := 118140960795 + 1615823 * 2 ^ 59
def prefixEnd_1615823 : Nat := 4983230072969 + 3 ^ 40 * 1615823 * 2
def baseEnd_1615823 : Nat := 829693851589936818781471

theorem tailTrace_1615823 : CollatzResearch.WordTrace tailWord_1615823 prefixEnd_1615823 829693851589936818781471 := by
  unfold tailWord_1615823
  simp only [CollatzResearch.WordTrace]
  refine ⟨58933906425156706443164123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39289270950104470962109415 58933906425156706443164123)
  ·
    refine ⟨88400859637735059664746185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58933906425156706443164123 88400859637735059664746185)
    ·
      refine ⟨66300644728301294748559639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88400859637735059664746185 66300644728301294748559639)
      ·
        refine ⟨99450967092451942122839459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66300644728301294748559639 99450967092451942122839459)
        ·
          refine ⟨149176450638677913184259189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99450967092451942122839459 149176450638677913184259189)
          ·
            refine ⟨13985292247376054361024299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149176450638677913184259189 13985292247376054361024299)
            ·
              refine ⟨20977938371064081541536449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13985292247376054361024299 20977938371064081541536449)
              ·
                refine ⟨15733453778298061156152337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20977938371064081541536449 15733453778298061156152337)
                ·
                  refine ⟨11800090333723545867114253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15733453778298061156152337 11800090333723545867114253)
                  ·
                    refine ⟨4425033875146329700167845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11800090333723545867114253 4425033875146329700167845)
                    ·
                      refine ⟨829693851589936818781471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4425033875146329700167845 829693851589936818781471)
                      ·
                        rfl

theorem cell23_1615823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_1615823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615823 prefixEnd_1615823 := by exact prefixLift 1615823
  have htrace : WordTrace (prefixWord ++ tailWord_1615823) baseStart_1615823 baseEnd_1615823 := by
    simpa [prefixWord, tailWord_1615823, baseEnd_1615823] using wordTrace_append hprefix tailTrace_1615823
  have hstable : (prefixWord ++ tailWord_1615823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615823).length < 2 ^ (prefixWord ++ tailWord_1615823).sum := by decide
  have hdescent : baseEnd_1615823 < baseStart_1615823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615920 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 5]
def baseStart_1615920 : Nat := 118140960795 + 1615920 * 2 ^ 59
def prefixEnd_1615920 : Nat := 4983230072969 + 3 ^ 40 * 1615920 * 2
def baseEnd_1615920 : Nat := 829743659213422939268525

theorem tailTrace_1615920 : CollatzResearch.WordTrace tailWord_1615920 prefixEnd_1615920 829743659213422939268525 := by
  unfold tailWord_1615920
  simp only [CollatzResearch.WordTrace]
  refine ⟨29468722152902646004722607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39291629537203528006296809 29468722152902646004722607)
  ·
    refine ⟨44203083229353969007083911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29468722152902646004722607 44203083229353969007083911)
    ·
      refine ⟨66304624844030953510625867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44203083229353969007083911 66304624844030953510625867)
      ·
        refine ⟨99456937266046430265938801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66304624844030953510625867 99456937266046430265938801)
        ·
          refine ⟨74592702949534822699454101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99456937266046430265938801 74592702949534822699454101)
          ·
            refine ⟨3496532950759444814036911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74592702949534822699454101 3496532950759444814036911)
            ·
              refine ⟨5244799426139167221055367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3496532950759444814036911 5244799426139167221055367)
              ·
                refine ⟨7867199139208750831583051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5244799426139167221055367 7867199139208750831583051)
                ·
                  refine ⟨11800798708813126247374577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7867199139208750831583051 11800798708813126247374577)
                  ·
                    refine ⟨8850599031609844685530933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11800798708813126247374577 8850599031609844685530933)
                    ·
                      refine ⟨829743659213422939268525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8850599031609844685530933 829743659213422939268525)
                      ·
                        rfl

theorem cell23_1615920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 5].length) (baseStart_1615920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615920 prefixEnd_1615920 := by exact prefixLift 1615920
  have htrace : WordTrace (prefixWord ++ tailWord_1615920) baseStart_1615920 baseEnd_1615920 := by
    simpa [prefixWord, tailWord_1615920, baseEnd_1615920] using wordTrace_append hprefix tailTrace_1615920
  have hstable : (prefixWord ++ tailWord_1615920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615920).length < 2 ^ (prefixWord ++ tailWord_1615920).sum := by decide
  have hdescent : baseEnd_1615920 < baseStart_1615920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615930 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4]
def baseStart_1615930 : Nat := 118140960795 + 1615930 * 2 ^ 59
def prefixEnd_1615930 : Nat := 4983230072969 + 3 ^ 40 * 1615930 * 2
def baseEnd_1615930 : Nat := 829748794019967900143479

theorem tailTrace_1615930 : CollatzResearch.WordTrace tailWord_1615930 prefixEnd_1615930 829748794019967900143479 := by
  unfold tailWord_1615930
  simp only [CollatzResearch.WordTrace]
  refine ⟨14734452258942265929327311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39291872690512709144872829 14734452258942265929327311)
  ·
    refine ⟨22101678388413398893990967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14734452258942265929327311 22101678388413398893990967)
    ·
      refine ⟨33152517582620098340986451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22101678388413398893990967 33152517582620098340986451)
      ·
        refine ⟨49728776373930147511479677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33152517582620098340986451 49728776373930147511479677)
        ·
          refine ⟨18648291140223805316804879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49728776373930147511479677 18648291140223805316804879)
          ·
            refine ⟨27972436710335707975207319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18648291140223805316804879 27972436710335707975207319)
            ·
              refine ⟨41958655065503561962810979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27972436710335707975207319 41958655065503561962810979)
              ·
                refine ⟨62937982598255342944216469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41958655065503561962810979 62937982598255342944216469)
                ·
                  refine ⟨2950217934293219200510147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62937982598255342944216469 2950217934293219200510147)
                  ·
                    refine ⟨4425326901439828800765221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2950217934293219200510147 4425326901439828800765221)
                    ·
                      refine ⟨829748794019967900143479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4425326901439828800765221 829748794019967900143479)
                      ·
                        rfl

theorem cell23_1615930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_1615930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615930 prefixEnd_1615930 := by exact prefixLift 1615930
  have htrace : WordTrace (prefixWord ++ tailWord_1615930) baseStart_1615930 baseEnd_1615930 := by
    simpa [prefixWord, tailWord_1615930, baseEnd_1615930] using wordTrace_append hprefix tailTrace_1615930
  have hstable : (prefixWord ++ tailWord_1615930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615930).length < 2 ^ (prefixWord ++ tailWord_1615930).sum := by decide
  have hdescent : baseEnd_1615930 < baseStart_1615930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616001 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_1616001 : Nat := 118140960795 + 1616001 * 2 ^ 59
def prefixEnd_1616001 : Nat := 4983230072969 + 3 ^ 40 * 1616001 * 2
def baseEnd_1616001 : Nat := 829785251146437122355653

theorem tailTrace_1616001 : CollatzResearch.WordTrace tailWord_1616001 prefixEnd_1616001 829785251146437122355653 := by
  unfold tailWord_1616001
  simp only [CollatzResearch.WordTrace]
  refine ⟨58940398618511842843143857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39293599079007895228762571 58940398618511842843143857)
  ·
    refine ⟨44205298963883882132357893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58940398618511842843143857 44205298963883882132357893)
    ·
      refine ⟨8288493555728227899817105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44205298963883882132357893 8288493555728227899817105)
      ·
        refine ⟨6216370166796170924862829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8288493555728227899817105 6216370166796170924862829)
        ·
          refine ⟨2331138812548564096823561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6216370166796170924862829 2331138812548564096823561)
          ·
            refine ⟨1748354109411423072617671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2331138812548564096823561 1748354109411423072617671)
            ·
              refine ⟨2622531164117134608926507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748354109411423072617671 2622531164117134608926507)
              ·
                refine ⟨3933796746175701913389761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622531164117134608926507 3933796746175701913389761)
                ·
                  refine ⟨2950347559631776435042321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3933796746175701913389761 2950347559631776435042321)
                  ·
                    refine ⟨2212760669723832326281741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2950347559631776435042321 2212760669723832326281741)
                    ·
                      refine ⟨829785251146437122355653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2212760669723832326281741 829785251146437122355653)
                      ·
                        rfl

theorem cell23_1616001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_1616001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616001 prefixEnd_1616001 := by exact prefixLift 1616001
  have htrace : WordTrace (prefixWord ++ tailWord_1616001) baseStart_1616001 baseEnd_1616001 := by
    simpa [prefixWord, tailWord_1616001, baseEnd_1616001] using wordTrace_append hprefix tailTrace_1616001
  have hstable : (prefixWord ++ tailWord_1616001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616001).length < 2 ^ (prefixWord ++ tailWord_1616001).sum := by decide
  have hdescent : baseEnd_1616001 < baseStart_1616001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616031 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 3, 1, 3]
def baseStart_1616031 : Nat := 118140960795 + 1616031 * 2 ^ 59
def prefixEnd_1616031 : Nat := 4983230072969 + 3 ^ 40 * 1616031 * 2
def baseEnd_1616031 : Nat := 829800655566072004980515

theorem tailTrace_1616031 : CollatzResearch.WordTrace tailWord_1616031 prefixEnd_1616031 829800655566072004980515 := by
  unfold tailWord_1616031
  simp only [CollatzResearch.WordTrace]
  refine ⟨58941492808403157966735947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39294328538935438644490631 58941492808403157966735947)
  ·
    refine ⟨88412239212604736950103921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58941492808403157966735947 88412239212604736950103921)
    ·
      refine ⟨66309179409453552712577941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88412239212604736950103921 66309179409453552712577941)
      ·
        refine ⟨3108242784818135283402091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66309179409453552712577941 3108242784818135283402091)
        ·
          refine ⟨4662364177227202925103137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3108242784818135283402091 4662364177227202925103137)
          ·
            refine ⟨3496773132920402193827353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4662364177227202925103137 3496773132920402193827353)
            ·
              refine ⟨2622579849690301645370515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3496773132920402193827353 2622579849690301645370515)
              ·
                refine ⟨3933869774535452468055773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622579849690301645370515 3933869774535452468055773)
                ·
                  refine ⟨1475201165450794675520915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3933869774535452468055773 1475201165450794675520915)
                  ·
                    refine ⟨2212801748176192013281373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1475201165450794675520915 2212801748176192013281373)
                    ·
                      refine ⟨829800655566072004980515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2212801748176192013281373 829800655566072004980515)
                      ·
                        rfl

theorem cell23_1616031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_1616031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616031 prefixEnd_1616031 := by exact prefixLift 1616031
  have htrace : WordTrace (prefixWord ++ tailWord_1616031) baseStart_1616031 baseEnd_1616031 := by
    simpa [prefixWord, tailWord_1616031, baseEnd_1616031] using wordTrace_append hprefix tailTrace_1616031
  have hstable : (prefixWord ++ tailWord_1616031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616031).length < 2 ^ (prefixWord ++ tailWord_1616031).sum := by decide
  have hdescent : baseEnd_1616031 < baseStart_1616031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616074 : List Nat := [3, 1, 2, 1, 3, 1, 1, 5, 1, 2, 3]
def baseStart_1616074 : Nat := 118140960795 + 1616074 * 2 ^ 59
def prefixEnd_1616074 : Nat := 4983230072969 + 3 ^ 40 * 1616074 * 2
def baseEnd_1616074 : Nat := 829822735234215336742817

theorem tailTrace_1616074 : CollatzResearch.WordTrace tailWord_1616074 prefixEnd_1616074 829822735234215336742817 := by
  unfold tailWord_1616074
  simp only [CollatzResearch.WordTrace]
  refine ⟨14735765286811844077637819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39295374098164917540367517 14735765286811844077637819)
  ·
    refine ⟨22103647930217766116456729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14735765286811844077637819 22103647930217766116456729)
    ·
      refine ⟨16577735947663324587342547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22103647930217766116456729 16577735947663324587342547)
      ·
        refine ⟨24866603921494986881013821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16577735947663324587342547 24866603921494986881013821)
        ·
          refine ⟨9324976470560620080380183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24866603921494986881013821 9324976470560620080380183)
          ·
            refine ⟨13987464705840930120570275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9324976470560620080380183 13987464705840930120570275)
            ·
              refine ⟨20981197058761395180855413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13987464705840930120570275 20981197058761395180855413)
              ·
                refine ⟨1966987224258880798205195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20981197058761395180855413 1966987224258880798205195)
                ·
                  refine ⟨2950480836388321197307793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966987224258880798205195 2950480836388321197307793)
                  ·
                    refine ⟨2212860627291240897980845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2950480836388321197307793 2212860627291240897980845)
                    ·
                      refine ⟨829822735234215336742817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2212860627291240897980845 829822735234215336742817)
                      ·
                        rfl

theorem cell23_1616074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_1616074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616074 prefixEnd_1616074 := by exact prefixLift 1616074
  have htrace : WordTrace (prefixWord ++ tailWord_1616074) baseStart_1616074 baseEnd_1616074 := by
    simpa [prefixWord, tailWord_1616074, baseEnd_1616074] using wordTrace_append hprefix tailTrace_1616074
  have hstable : (prefixWord ++ tailWord_1616074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616074).length < 2 ^ (prefixWord ++ tailWord_1616074).sum := by decide
  have hdescent : baseEnd_1616074 < baseStart_1616074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616088 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 3, 2, 2]
def baseStart_1616088 : Nat := 118140960795 + 1616088 * 2 ^ 59
def prefixEnd_1616088 : Nat := 4983230072969 + 3 ^ 40 * 1616088 * 2
def baseEnd_1616088 : Nat := 829829923963378281967753

theorem tailTrace_1616088 : CollatzResearch.WordTrace tailWord_1616088 prefixEnd_1616088 829829923963378281967753 := by
  unfold tailWord_1616088
  simp only [CollatzResearch.WordTrace]
  refine ⟨29471785884598328350780459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39295714512797771134373945 29471785884598328350780459)
  ·
    refine ⟨44207678826897492526170689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29471785884598328350780459 44207678826897492526170689)
    ·
      refine ⟨33155759120173119394628017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44207678826897492526170689 33155759120173119394628017)
      ·
        refine ⟨24866819340129839545971013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33155759120173119394628017 24866819340129839545971013)
        ·
          refine ⟨4662528626274344914869565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24866819340129839545971013 4662528626274344914869565)
          ·
            refine ⟨1748448234852879343076087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4662528626274344914869565 1748448234852879343076087)
            ·
              refine ⟨2622672352279319014614131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748448234852879343076087 2622672352279319014614131)
              ·
                refine ⟨3934008528418978521921197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622672352279319014614131 3934008528418978521921197)
                ·
                  refine ⟨1475253198157116945720449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3934008528418978521921197 1475253198157116945720449)
                  ·
                    refine ⟨1106439898617837709290337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1475253198157116945720449 1106439898617837709290337)
                    ·
                      refine ⟨829829923963378281967753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1106439898617837709290337 829829923963378281967753)
                      ·
                        rfl

theorem cell23_1616088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_1616088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616088 prefixEnd_1616088 := by exact prefixLift 1616088
  have htrace : WordTrace (prefixWord ++ tailWord_1616088) baseStart_1616088 baseEnd_1616088 := by
    simpa [prefixWord, tailWord_1616088, baseEnd_1616088] using wordTrace_append hprefix tailTrace_1616088
  have hstable : (prefixWord ++ tailWord_1616088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616088).length < 2 ^ (prefixWord ++ tailWord_1616088).sum := by decide
  have hdescent : baseEnd_1616088 < baseStart_1616088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616154 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 2, 6]
def baseStart_1616154 : Nat := 118140960795 + 1616154 * 2 ^ 59
def prefixEnd_1616154 : Nat := 4983230072969 + 3 ^ 40 * 1616154 * 2
def baseEnd_1616154 : Nat := 276621271228858341247483

theorem tailTrace_1616154 : CollatzResearch.WordTrace tailWord_1616154 prefixEnd_1616154 276621271228858341247483 := by
  unfold tailWord_1616154
  simp only [CollatzResearch.WordTrace]
  refine ⟨14736494746739387493365879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39297319324638366648975677 14736494746739387493365879)
  ·
    refine ⟨22104742120109081240048819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14736494746739387493365879 22104742120109081240048819)
    ·
      refine ⟨33157113180163621860073229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22104742120109081240048819 33157113180163621860073229)
      ·
        refine ⟨12433917442561358197527461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33157113180163621860073229 12433917442561358197527461)
        ·
          refine ⟨2331359520480254662036399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12433917442561358197527461 2331359520480254662036399)
          ·
            refine ⟨3497039280720381993054599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331359520480254662036399 3497039280720381993054599)
            ·
              refine ⟨5245558921080572989581899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3497039280720381993054599 5245558921080572989581899)
              ·
                refine ⟨7868338381620859484372849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5245558921080572989581899 7868338381620859484372849)
                ·
                  refine ⟨5901253786215644613279637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7868338381620859484372849 5901253786215644613279637)
                  ·
                    refine ⟨276621271228858341247483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5901253786215644613279637 276621271228858341247483)
                    ·
                      rfl

theorem cell23_1616154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_1616154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616154 prefixEnd_1616154 := by exact prefixLift 1616154
  have htrace : WordTrace (prefixWord ++ tailWord_1616154) baseStart_1616154 baseEnd_1616154 := by
    simpa [prefixWord, tailWord_1616154, baseEnd_1616154] using wordTrace_append hprefix tailTrace_1616154
  have hstable : (prefixWord ++ tailWord_1616154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616154).length < 2 ^ (prefixWord ++ tailWord_1616154).sum := by decide
  have hdescent : baseEnd_1616154 < baseStart_1616154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616184 : List Nat := [2, 1, 2, 1, 3, 1, 3, 5, 5]
def baseStart_1616184 : Nat := 118140960795 + 1616184 * 2 ^ 59
def prefixEnd_1616184 : Nat := 4983230072969 + 3 ^ 40 * 1616184 * 2
def baseEnd_1616184 : Nat := 92208802011801100707479

theorem tailTrace_1616184 : CollatzResearch.WordTrace tailWord_1616184 prefixEnd_1616184 92208802011801100707479 := by
  unfold tailWord_1616184
  simp only [CollatzResearch.WordTrace]
  refine ⟨29473536588424432548527803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39298048784565910064703737 29473536588424432548527803)
  ·
    refine ⟨44210304882636648822791705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29473536588424432548527803 44210304882636648822791705)
    ·
      refine ⟨33157728661977486617093779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44210304882636648822791705 33157728661977486617093779)
      ·
        refine ⟨49736592992966229925640669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33157728661977486617093779 49736592992966229925640669)
        ·
          refine ⟨18651222372362336222115251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49736592992966229925640669 18651222372362336222115251)
          ·
            refine ⟨27976833558543504333172877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18651222372362336222115251 27976833558543504333172877)
            ·
              refine ⟨10491312584453814124939829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27976833558543504333172877 10491312584453814124939829)
              ·
                refine ⟨983560554792545074213109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10491312584453814124939829 983560554792545074213109)
                ·
                  refine ⟨92208802011801100707479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 983560554792545074213109 92208802011801100707479)
                  ·
                    rfl

theorem cell23_1616184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 5].length) (baseStart_1616184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616184 prefixEnd_1616184 := by exact prefixLift 1616184
  have htrace : WordTrace (prefixWord ++ tailWord_1616184) baseStart_1616184 baseEnd_1616184 := by
    simpa [prefixWord, tailWord_1616184, baseEnd_1616184] using wordTrace_append hprefix tailTrace_1616184
  have hstable : (prefixWord ++ tailWord_1616184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616184).length < 2 ^ (prefixWord ++ tailWord_1616184).sum := by decide
  have hdescent : baseEnd_1616184 < baseStart_1616184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616227 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 2, 8]
def baseStart_1616227 : Nat := 118140960795 + 1616227 * 2 ^ 59
def prefixEnd_1616227 : Nat := 4983230072969 + 3 ^ 40 * 1616227 * 2
def baseEnd_1616227 : Nat := 276633765924784412709871

theorem tailTrace_1616227 : CollatzResearch.WordTrace tailWord_1616227 prefixEnd_1616227 276633765924784412709871 := by
  unfold tailWord_1616227
  simp only [CollatzResearch.WordTrace]
  refine ⟨58948641515693083440870935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39299094343795388960580623 58948641515693083440870935)
  ·
    refine ⟨88422962273539625161306403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58948641515693083440870935 88422962273539625161306403)
    ·
      refine ⟨132634443410309437741959605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88422962273539625161306403 132634443410309437741959605)
      ·
        refine ⟨12434479069716509788308713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132634443410309437741959605 12434479069716509788308713)
        ·
          refine ⟨9325859302287382341231535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12434479069716509788308713 9325859302287382341231535)
          ·
            refine ⟨13988788953431073511847303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9325859302287382341231535 13988788953431073511847303)
            ·
              refine ⟨20983183430146610267770955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13988788953431073511847303 20983183430146610267770955)
              ·
                refine ⟨31474775145219915401656433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20983183430146610267770955 31474775145219915401656433)
                ·
                  refine ⟨23606081358914936551242325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31474775145219915401656433 23606081358914936551242325)
                  ·
                    refine ⟨276633765924784412709871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23606081358914936551242325 276633765924784412709871)
                    ·
                      rfl

theorem cell23_1616227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 8].length) (baseStart_1616227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616227 prefixEnd_1616227 := by exact prefixLift 1616227
  have htrace : WordTrace (prefixWord ++ tailWord_1616227) baseStart_1616227 baseEnd_1616227 := by
    simpa [prefixWord, tailWord_1616227, baseEnd_1616227] using wordTrace_append hprefix tailTrace_1616227
  have hstable : (prefixWord ++ tailWord_1616227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616227).length < 2 ^ (prefixWord ++ tailWord_1616227).sum := by decide
  have hdescent : baseEnd_1616227 < baseStart_1616227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616247 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 6]
def baseStart_1616247 : Nat := 118140960795 + 1616247 * 2 ^ 59
def prefixEnd_1616247 : Nat := 4983230072969 + 3 ^ 40 * 1616247 * 2
def baseEnd_1616247 : Nat := 829911567387443159879521

theorem tailTrace_1616247 : CollatzResearch.WordTrace tailWord_1616247 prefixEnd_1616247 829911567387443159879521 := by
  unfold tailWord_1616247
  simp only [CollatzResearch.WordTrace]
  refine ⟨58949370975620626856598995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39299580650413751237732663 58949370975620626856598995)
  ·
    refine ⟨88424056463430940284898493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58949370975620626856598995 88424056463430940284898493)
    ·
      refine ⟨33159021173786602606836935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88424056463430940284898493 33159021173786602606836935)
      ·
        refine ⟨49738531760679903910255403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33159021173786602606836935 49738531760679903910255403)
        ·
          refine ⟨74607797641019855865383105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49738531760679903910255403 74607797641019855865383105)
          ·
            refine ⟨55955848230764891899037329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74607797641019855865383105 55955848230764891899037329)
            ·
              refine ⟨41966886173073668924277997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55955848230764891899037329 41966886173073668924277997)
              ·
                refine ⟨15737582314902625846604249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41966886173073668924277997 15737582314902625846604249)
                ·
                  refine ⟨11803186736176969384953187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15737582314902625846604249 11803186736176969384953187)
                  ·
                    refine ⟨17704780104265454077429781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11803186736176969384953187 17704780104265454077429781)
                    ·
                      refine ⟨829911567387443159879521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17704780104265454077429781 829911567387443159879521)
                      ·
                        rfl

theorem cell23_1616247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_1616247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616247 prefixEnd_1616247 := by exact prefixLift 1616247
  have htrace : WordTrace (prefixWord ++ tailWord_1616247) baseStart_1616247 baseEnd_1616247 := by
    simpa [prefixWord, tailWord_1616247, baseEnd_1616247] using wordTrace_append hprefix tailTrace_1616247
  have hstable : (prefixWord ++ tailWord_1616247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616247).length < 2 ^ (prefixWord ++ tailWord_1616247).sum := by decide
  have hdescent : baseEnd_1616247 < baseStart_1616247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616258 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_1616258 : Nat := 118140960795 + 1616258 * 2 ^ 59
def prefixEnd_1616258 : Nat := 4983230072969 + 3 ^ 40 * 1616258 * 2
def baseEnd_1616258 : Nat := 829917215674642616841971

theorem tailTrace_1616258 : CollatzResearch.WordTrace tailWord_1616258 prefixEnd_1616258 829917215674642616841971 := by
  unfold tailWord_1616258
  simp only [CollatzResearch.WordTrace]
  refine ⟨14737443044645193933812357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39299848119053850490166285 14737443044645193933812357)
  ·
    refine ⟨2763270570870973862589817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14737443044645193933812357 2763270570870973862589817)
    ·
      refine ⟨2072452928153230396942363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2763270570870973862589817 2072452928153230396942363)
      ·
        refine ⟨3108679392229845595413545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2072452928153230396942363 3108679392229845595413545)
        ·
          refine ⟨2331509544172384196560159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3108679392229845595413545 2331509544172384196560159)
          ·
            refine ⟨3497264316258576294840239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331509544172384196560159 3497264316258576294840239)
            ·
              refine ⟨5245896474387864442260359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3497264316258576294840239 5245896474387864442260359)
              ·
                refine ⟨7868844711581796663390539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5245896474387864442260359 7868844711581796663390539)
                ·
                  refine ⟨11803267067372694995085809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7868844711581796663390539 11803267067372694995085809)
                  ·
                    refine ⟨8852450300529521246314357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11803267067372694995085809 8852450300529521246314357)
                    ·
                      refine ⟨829917215674642616841971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8852450300529521246314357 829917215674642616841971)
                      ·
                        rfl

theorem cell23_1616258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_1616258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616258 prefixEnd_1616258 := by exact prefixLift 1616258
  have htrace : WordTrace (prefixWord ++ tailWord_1616258) baseStart_1616258 baseEnd_1616258 := by
    simpa [prefixWord, tailWord_1616258, baseEnd_1616258] using wordTrace_append hprefix tailTrace_1616258
  have hstable : (prefixWord ++ tailWord_1616258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616258).length < 2 ^ (prefixWord ++ tailWord_1616258).sum := by decide
  have hdescent : baseEnd_1616258 < baseStart_1616258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616297 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 7]
def baseStart_1616297 : Nat := 118140960795 + 1616297 * 2 ^ 59
def prefixEnd_1616297 : Nat := 4983230072969 + 3 ^ 40 * 1616297 * 2
def baseEnd_1616297 : Nat := 829937241420167964254291

theorem tailTrace_1616297 : CollatzResearch.WordTrace tailWord_1616297 prefixEnd_1616297 829937241420167964254291 := by
  unfold tailWord_1616297
  simp only [CollatzResearch.WordTrace]
  refine ⟨58951194625439485395919145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39300796416959656930612763 58951194625439485395919145)
  ·
    refine ⟨44213395969079614046939359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58951194625439485395919145 44213395969079614046939359)
    ·
      refine ⟨66320093953619421070409039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44213395969079614046939359 66320093953619421070409039)
      ·
        refine ⟨99480140930429131605613559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66320093953619421070409039 99480140930429131605613559)
        ·
          refine ⟨149220211395643697408420339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99480140930429131605613559 149220211395643697408420339)
          ·
            refine ⟨223830317093465546112630509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149220211395643697408420339 223830317093465546112630509)
            ·
              refine ⟨83936368910049579792236441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223830317093465546112630509 83936368910049579792236441)
              ·
                refine ⟨62952276682537184844177331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83936368910049579792236441 62952276682537184844177331)
                ·
                  refine ⟨94428415023805777266265997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62952276682537184844177331 94428415023805777266265997)
                  ·
                    refine ⟨35410655633927166474849749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94428415023805777266265997 35410655633927166474849749)
                    ·
                      refine ⟨829937241420167964254291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35410655633927166474849749 829937241420167964254291)
                      ·
                        rfl

theorem cell23_1616297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_1616297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616297 prefixEnd_1616297 := by exact prefixLift 1616297
  have htrace : WordTrace (prefixWord ++ tailWord_1616297) baseStart_1616297 baseEnd_1616297 := by
    simpa [prefixWord, tailWord_1616297, baseEnd_1616297] using wordTrace_append hprefix tailTrace_1616297
  have hstable : (prefixWord ++ tailWord_1616297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616297).length < 2 ^ (prefixWord ++ tailWord_1616297).sum := by decide
  have hdescent : baseEnd_1616297 < baseStart_1616297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616341 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_1616341 : Nat := 118140960795 + 1616341 * 2 ^ 59
def prefixEnd_1616341 : Nat := 4983230072969 + 3 ^ 40 * 1616341 * 2
def baseEnd_1616341 : Nat := 829959834568965792104089

theorem tailTrace_1616341 : CollatzResearch.WordTrace tailWord_1616341 prefixEnd_1616341 829959834568965792104089 := by
  unfold tailWord_1616341
  simp only [CollatzResearch.WordTrace]
  refine ⟨58952799437280080910520877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39301866291520053940347251 58952799437280080910520877)
  ·
    refine ⟨22107299788980030341445329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58952799437280080910520877 22107299788980030341445329)
    ·
      refine ⟨16580474841735022756083997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22107299788980030341445329 16580474841735022756083997)
      ·
        refine ⟨6217678065650633533531499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16580474841735022756083997 6217678065650633533531499)
        ·
          refine ⟨9326517098475950300297249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6217678065650633533531499 9326517098475950300297249)
          ·
            refine ⟨6994887823856962725222937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9326517098475950300297249 6994887823856962725222937)
            ·
              refine ⟨5246165867892722043917203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6994887823856962725222937 5246165867892722043917203)
              ·
                refine ⟨7869248801839083065875805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5246165867892722043917203 7869248801839083065875805)
                ·
                  refine ⟨2950968300689656149703427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7869248801839083065875805 2950968300689656149703427)
                  ·
                    refine ⟨4426452451034484224555141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2950968300689656149703427 4426452451034484224555141)
                    ·
                      refine ⟨829959834568965792104089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4426452451034484224555141 829959834568965792104089)
                      ·
                        rfl

theorem cell23_1616341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_1616341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616341 prefixEnd_1616341 := by exact prefixLift 1616341
  have htrace : WordTrace (prefixWord ++ tailWord_1616341) baseStart_1616341 baseEnd_1616341 := by
    simpa [prefixWord, tailWord_1616341, baseEnd_1616341] using wordTrace_append hprefix tailTrace_1616341
  have hstable : (prefixWord ++ tailWord_1616341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616341).length < 2 ^ (prefixWord ++ tailWord_1616341).sum := by decide
  have hdescent : baseEnd_1616341 < baseStart_1616341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616355 : List Nat := [1, 1, 1, 6, 3, 2, 2, 1, 1, 5]
def baseStart_1616355 : Nat := 118140960795 + 1616355 * 2 ^ 59
def prefixEnd_1616355 : Nat := 4983230072969 + 3 ^ 40 * 1616355 * 2
def baseEnd_1616355 : Nat := 276655674432709579109675

theorem tailTrace_1616355 : CollatzResearch.WordTrace tailWord_1616355 prefixEnd_1616355 276655674432709579109675 := by
  unfold tailWord_1616355
  simp only [CollatzResearch.WordTrace]
  refine ⟨58953310059229361301530519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39302206706152907534353679 58953310059229361301530519)
  ·
    refine ⟨88429965088844041952295779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58953310059229361301530519 88429965088844041952295779)
    ·
      refine ⟨132644947633266062928443669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88429965088844041952295779 132644947633266062928443669)
      ·
        refine ⟨6217731920309346699770797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 132644947633266062928443669 6217731920309346699770797)
        ·
          refine ⟨2331649470116005012414049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6217731920309346699770797 2331649470116005012414049)
          ·
            refine ⟨1748737102587003759310537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2331649470116005012414049 1748737102587003759310537)
            ·
              refine ⟨1311552826940252819482903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1748737102587003759310537 1311552826940252819482903)
              ·
                refine ⟨1967329240410379229224355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311552826940252819482903 1967329240410379229224355)
                ·
                  refine ⟨2950993860615568843836533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1967329240410379229224355 2950993860615568843836533)
                  ·
                    refine ⟨276655674432709579109675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2950993860615568843836533 276655674432709579109675)
                    ·
                      rfl

theorem cell23_1616355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 1, 5].length) (baseStart_1616355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616355 prefixEnd_1616355 := by exact prefixLift 1616355
  have htrace : WordTrace (prefixWord ++ tailWord_1616355) baseStart_1616355 baseEnd_1616355 := by
    simpa [prefixWord, tailWord_1616355, baseEnd_1616355] using wordTrace_append hprefix tailTrace_1616355
  have hstable : (prefixWord ++ tailWord_1616355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616355).length < 2 ^ (prefixWord ++ tailWord_1616355).sum := by decide
  have hdescent : baseEnd_1616355 < baseStart_1616355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616385 : List Nat := [1, 2, 4, 1, 3, 2, 3, 1, 2, 4]
def baseStart_1616385 : Nat := 118140960795 + 1616385 * 2 ^ 59
def prefixEnd_1616385 : Nat := 4983230072969 + 3 ^ 40 * 1616385 * 2
def baseEnd_1616385 : Nat := 276660809239254539984629

theorem tailTrace_1616385 : CollatzResearch.WordTrace tailWord_1616385 prefixEnd_1616385 276660809239254539984629 := by
  unfold tailWord_1616385
  simp only [CollatzResearch.WordTrace]
  refine ⟨58954404249120676425122609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39302936166080450950081739 58954404249120676425122609)
  ·
    refine ⟨44215803186840507318841957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58954404249120676425122609 44215803186840507318841957)
    ·
      refine ⟨8290463097532595122282867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44215803186840507318841957 8290463097532595122282867)
      ·
        refine ⟨12435694646298892683424301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8290463097532595122282867 12435694646298892683424301)
        ·
          refine ⟨4663385492362084756284113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12435694646298892683424301 4663385492362084756284113)
          ·
            refine ⟨3497539119271563567213085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4663385492362084756284113 3497539119271563567213085)
            ·
              refine ⟨1311577169726836337704907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3497539119271563567213085 1311577169726836337704907)
              ·
                refine ⟨1967365754590254506557361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311577169726836337704907 1967365754590254506557361)
                ·
                  refine ⟨1475524315942690879918021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1967365754590254506557361 1475524315942690879918021)
                  ·
                    refine ⟨276660809239254539984629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1475524315942690879918021 276660809239254539984629)
                    ·
                      rfl

theorem cell23_1616385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_1616385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616385 prefixEnd_1616385 := by exact prefixLift 1616385
  have htrace : WordTrace (prefixWord ++ tailWord_1616385) baseStart_1616385 baseEnd_1616385 := by
    simpa [prefixWord, tailWord_1616385, baseEnd_1616385] using wordTrace_append hprefix tailTrace_1616385
  have hstable : (prefixWord ++ tailWord_1616385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616385).length < 2 ^ (prefixWord ++ tailWord_1616385).sum := by decide
  have hdescent : baseEnd_1616385 < baseStart_1616385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616388 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1616388 : Nat := 118140960795 + 1616388 * 2 ^ 59
def prefixEnd_1616388 : Nat := 4983230072969 + 3 ^ 40 * 1616388 * 2
def baseEnd_1616388 : Nat := 829983968159727108216373

theorem tailTrace_1616388 : CollatzResearch.WordTrace tailWord_1616388 prefixEnd_1616388 829983968159727108216373 := by
  unfold tailWord_1616388
  simp only [CollatzResearch.WordTrace]
  refine ⟨29477256834054903968740909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39303009112073205291654545 29477256834054903968740909)
  ·
    refine ⟨11053971312770588988277841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29477256834054903968740909 11053971312770588988277841)
    ·
      refine ⟨8290478484577941741208381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11053971312770588988277841 8290478484577941741208381)
      ·
        refine ⟨3108929431716728152953143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8290478484577941741208381 3108929431716728152953143)
        ·
          refine ⟨4663394147575092229429715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3108929431716728152953143 4663394147575092229429715)
          ·
            refine ⟨6995091221362638344144573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4663394147575092229429715 6995091221362638344144573)
            ·
              refine ⟨2623159208010989379054215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6995091221362638344144573 2623159208010989379054215)
              ·
                refine ⟨3934738812016484068581323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2623159208010989379054215 3934738812016484068581323)
                ·
                  refine ⟨5902108218024726102871985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3934738812016484068581323 5902108218024726102871985)
                  ·
                    refine ⟨4426581163518544577153989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5902108218024726102871985 4426581163518544577153989)
                    ·
                      refine ⟨829983968159727108216373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4426581163518544577153989 829983968159727108216373)
                      ·
                        rfl

theorem cell23_1616388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1616388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616388 prefixEnd_1616388 := by exact prefixLift 1616388
  have htrace : WordTrace (prefixWord ++ tailWord_1616388) baseStart_1616388 baseEnd_1616388 := by
    simpa [prefixWord, tailWord_1616388, baseEnd_1616388] using wordTrace_append hprefix tailTrace_1616388
  have hstable : (prefixWord ++ tailWord_1616388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616388).length < 2 ^ (prefixWord ++ tailWord_1616388).sum := by decide
  have hdescent : baseEnd_1616388 < baseStart_1616388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616398 : List Nat := [4, 1, 1, 2, 3, 3, 2, 7]
def baseStart_1616398 : Nat := 118140960795 + 1616398 * 2 ^ 59
def prefixEnd_1616398 : Nat := 4983230072969 + 3 ^ 40 * 1616398 * 2
def baseEnd_1616398 : Nat := 30740337146898965521901

theorem tailTrace_1616398 : CollatzResearch.WordTrace tailWord_1616398 prefixEnd_1616398 30740337146898965521901 := by
  unfold tailWord_1616398
  simp only [CollatzResearch.WordTrace]
  refine ⟨7369359799759197455668231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39303252265382386430230565 7369359799759197455668231)
  ·
    refine ⟨11054039699638796183502347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7369359799759197455668231 11054039699638796183502347)
    ·
      refine ⟨16581059549458194275253521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11054039699638796183502347 16581059549458194275253521)
      ·
        refine ⟨12435794662093645706440141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16581059549458194275253521 12435794662093645706440141)
        ·
          refine ⟨4663422998285117139915053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12435794662093645706440141 4663422998285117139915053)
          ·
            refine ⟨1748783624356918927468145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4663422998285117139915053 1748783624356918927468145)
            ·
              refine ⟨1311587718267689195601109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1748783624356918927468145 1311587718267689195601109)
              ·
                refine ⟨30740337146898965521901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1311587718267689195601109 30740337146898965521901)
                ·
                  rfl

theorem cell23_1616398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 7].length) (baseStart_1616398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616398 prefixEnd_1616398 := by exact prefixLift 1616398
  have htrace : WordTrace (prefixWord ++ tailWord_1616398) baseStart_1616398 baseEnd_1616398 := by
    simpa [prefixWord, tailWord_1616398, baseEnd_1616398] using wordTrace_append hprefix tailTrace_1616398
  have hstable : (prefixWord ++ tailWord_1616398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616398).length < 2 ^ (prefixWord ++ tailWord_1616398).sum := by decide
  have hdescent : baseEnd_1616398 < baseStart_1616398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616408 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 4, 1, 3]
def baseStart_1616408 : Nat := 118140960795 + 1616408 * 2 ^ 59
def prefixEnd_1616408 : Nat := 4983230072969 + 3 ^ 40 * 1616408 * 2
def baseEnd_1616408 : Nat := 829994237772817029966281

theorem tailTrace_1616408 : CollatzResearch.WordTrace tailWord_1616408 prefixEnd_1616408 829994237772817029966281 := by
  unfold tailWord_1616408
  simp only [CollatzResearch.WordTrace]
  refine ⟨29477621564018675676604939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39303495418691567568806585 29477621564018675676604939)
  ·
    refine ⟨44216432346028013514907409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29477621564018675676604939 44216432346028013514907409)
    ·
      refine ⟨33162324259521010136180557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44216432346028013514907409 33162324259521010136180557)
      ·
        refine ⟨12435871597320378801067709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33162324259521010136180557 12435871597320378801067709)
        ·
          refine ⟨4663451848995142050400391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12435871597320378801067709 4663451848995142050400391)
          ·
            refine ⟨6995177773492713075600587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4663451848995142050400391 6995177773492713075600587)
            ·
              refine ⟨10492766660239069613400881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6995177773492713075600587 10492766660239069613400881)
              ·
                refine ⟨7869574995179302210050661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10492766660239069613400881 7869574995179302210050661)
                ·
                  refine ⟨1475545311596119164384499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7869574995179302210050661 1475545311596119164384499)
                  ·
                    refine ⟨2213317967394178746576749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1475545311596119164384499 2213317967394178746576749)
                    ·
                      refine ⟨829994237772817029966281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2213317967394178746576749 829994237772817029966281)
                      ·
                        rfl

theorem cell23_1616408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_1616408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616408 prefixEnd_1616408 := by exact prefixLift 1616408
  have htrace : WordTrace (prefixWord ++ tailWord_1616408) baseStart_1616408 baseEnd_1616408 := by
    simpa [prefixWord, tailWord_1616408, baseEnd_1616408] using wordTrace_append hprefix tailTrace_1616408
  have hstable : (prefixWord ++ tailWord_1616408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616408).length < 2 ^ (prefixWord ++ tailWord_1616408).sum := by decide
  have hdescent : baseEnd_1616408 < baseStart_1616408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616418 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 5, 3, 2]
def baseStart_1616418 : Nat := 118140960795 + 1616418 * 2 ^ 59
def prefixEnd_1616418 : Nat := 4983230072969 + 3 ^ 40 * 1616418 * 2
def baseEnd_1616418 : Nat := 829999372579361990841235

theorem tailTrace_1616418 : CollatzResearch.WordTrace tailWord_1616418 prefixEnd_1616418 829999372579361990841235 := by
  unfold tailWord_1616418
  simp only [CollatzResearch.WordTrace]
  refine ⟨14738901964500280765268477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39303738572000748707382605 14738901964500280765268477)
  ·
    refine ⟨5527088236687605286975679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14738901964500280765268477 5527088236687605286975679)
    ·
      refine ⟨8290632355031407930463519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5527088236687605286975679 8290632355031407930463519)
      ·
        refine ⟨12435948532547111895695279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8290632355031407930463519 12435948532547111895695279)
        ·
          refine ⟨18653922798820667843542919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12435948532547111895695279 18653922798820667843542919)
          ·
            refine ⟨27980884198231001765314379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18653922798820667843542919 27980884198231001765314379)
            ·
              refine ⟨41971326297346502647971569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27980884198231001765314379 41971326297346502647971569)
              ·
                refine ⟨31478494723009876985978677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41971326297346502647971569 31478494723009876985978677)
                ·
                  refine ⟨2951108880282175967435501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31478494723009876985978677 2951108880282175967435501)
                  ·
                    refine ⟨1106665830105815987788313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2951108880282175967435501 1106665830105815987788313)
                    ·
                      refine ⟨829999372579361990841235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1106665830105815987788313 829999372579361990841235)
                      ·
                        rfl

theorem cell23_1616418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_1616418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616418 prefixEnd_1616418 := by exact prefixLift 1616418
  have htrace : WordTrace (prefixWord ++ tailWord_1616418) baseStart_1616418 baseEnd_1616418 := by
    simpa [prefixWord, tailWord_1616418, baseEnd_1616418] using wordTrace_append hprefix tailTrace_1616418
  have hstable : (prefixWord ++ tailWord_1616418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616418).length < 2 ^ (prefixWord ++ tailWord_1616418).sum := by decide
  have hdescent : baseEnd_1616418 < baseStart_1616418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616436 : List Nat := [2, 5, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_1616436 : Nat := 118140960795 + 1616436 * 2 ^ 59
def prefixEnd_1616436 : Nat := 4983230072969 + 3 ^ 40 * 1616436 * 2
def baseEnd_1616436 : Nat := 276669538410380973472051

theorem tailTrace_1616436 : CollatzResearch.WordTrace tailWord_1616436 prefixEnd_1616436 276669538410380973472051 := by
  unfold tailWord_1616436
  simp only [CollatzResearch.WordTrace]
  refine ⟨29478132185967956067614581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39304176247957274756819441 29478132185967956067614581)
  ·
    refine ⟨2763574892434495881338867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29478132185967956067614581 2763574892434495881338867)
    ·
      refine ⟨4145362338651743822008301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2763574892434495881338867 4145362338651743822008301)
      ·
        refine ⟨1554510876994403933253113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4145362338651743822008301 1554510876994403933253113)
        ·
          refine ⟨1165883157745802949939835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1554510876994403933253113 1165883157745802949939835)
          ·
            refine ⟨1748824736618704424909753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165883157745802949939835 1748824736618704424909753)
            ·
              refine ⟨1311618552464028318682315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1748824736618704424909753 1311618552464028318682315)
              ·
                refine ⟨1967427828696042478023473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311618552464028318682315 1967427828696042478023473)
                ·
                  refine ⟨1475570871522031858517605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1967427828696042478023473 1475570871522031858517605)
                  ·
                    refine ⟨276669538410380973472051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1475570871522031858517605 276669538410380973472051)
                    ·
                      rfl

theorem cell23_1616436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_1616436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616436 prefixEnd_1616436 := by exact prefixLift 1616436
  have htrace : WordTrace (prefixWord ++ tailWord_1616436) baseStart_1616436 baseEnd_1616436 := by
    simpa [prefixWord, tailWord_1616436, baseEnd_1616436] using wordTrace_append hprefix tailTrace_1616436
  have hstable : (prefixWord ++ tailWord_1616436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616436).length < 2 ^ (prefixWord ++ tailWord_1616436).sum := by decide
  have hdescent : baseEnd_1616436 < baseStart_1616436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616442 : List Nat := [3, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3]
def baseStart_1616442 : Nat := 118140960795 + 1616442 * 2 ^ 59
def prefixEnd_1616442 : Nat := 4983230072969 + 3 ^ 40 * 1616442 * 2
def baseEnd_1616442 : Nat := 830011696115069896941125

theorem tailTrace_1616442 : CollatzResearch.WordTrace tailWord_1616442 prefixEnd_1616442 830011696115069896941125 := by
  unfold tailWord_1616442
  simp only [CollatzResearch.WordTrace]
  refine ⟨14739120802478543789986895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39304322139942783439965053 14739120802478543789986895)
  ·
    refine ⟨22108681203717815684980343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14739120802478543789986895 22108681203717815684980343)
    ·
      refine ⟨33163021805576723527470515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22108681203717815684980343 33163021805576723527470515)
      ·
        refine ⟨49744532708365085291205773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33163021805576723527470515 49744532708365085291205773)
        ·
          refine ⟨18654199765636906984202165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49744532708365085291205773 18654199765636906984202165)
          ·
            refine ⟨1748831228028460029768953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18654199765636906984202165 1748831228028460029768953)
            ·
              refine ⟨1311623421021345022326715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1748831228028460029768953 1311623421021345022326715)
              ·
                refine ⟨1967435131532017533490073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311623421021345022326715 1967435131532017533490073)
                ·
                  refine ⟨1475576348649013150117555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1967435131532017533490073 1475576348649013150117555)
                  ·
                    refine ⟨2213364522973519725176333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1475576348649013150117555 2213364522973519725176333)
                    ·
                      refine ⟨830011696115069896941125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2213364522973519725176333 830011696115069896941125)
                      ·
                        rfl

theorem cell23_1616442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3].length) (baseStart_1616442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616442 prefixEnd_1616442 := by exact prefixLift 1616442
  have htrace : WordTrace (prefixWord ++ tailWord_1616442) baseStart_1616442 baseEnd_1616442 := by
    simpa [prefixWord, tailWord_1616442, baseEnd_1616442] using wordTrace_append hprefix tailTrace_1616442
  have hstable : (prefixWord ++ tailWord_1616442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616442).length < 2 ^ (prefixWord ++ tailWord_1616442).sum := by decide
  have hdescent : baseEnd_1616442 < baseStart_1616442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616464 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 7]
def baseStart_1616464 : Nat := 118140960795 + 1616464 * 2 ^ 59
def prefixEnd_1616464 : Nat := 4983230072969 + 3 ^ 40 * 1616464 * 2
def baseEnd_1616464 : Nat := 830022992689468810866023

theorem tailTrace_1616464 : CollatzResearch.WordTrace tailWord_1616464 prefixEnd_1616464 830022992689468810866023 := by
  unfold tailWord_1616464
  simp only [CollatzResearch.WordTrace]
  refine ⟨29478642807917236458624223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39304857077222981944832297 29478642807917236458624223)
  ·
    refine ⟨44217964211875854687936335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29478642807917236458624223 44217964211875854687936335)
    ·
      refine ⟨66326946317813782031904503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44217964211875854687936335 66326946317813782031904503)
      ·
        refine ⟨99490419476720673047856755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66326946317813782031904503 99490419476720673047856755)
        ·
          refine ⟨149235629215081009571785133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99490419476720673047856755 149235629215081009571785133)
          ·
            refine ⟨55963360955655378589419425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149235629215081009571785133 55963360955655378589419425)
            ·
              refine ⟨41972520716741533942064569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55963360955655378589419425 41972520716741533942064569)
              ·
                refine ⟨31479390537556150456548427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41972520716741533942064569 31479390537556150456548427)
                ·
                  refine ⟨47219085806334225684822641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31479390537556150456548427 47219085806334225684822641)
                  ·
                    refine ⟨35414314354750669263616981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47219085806334225684822641 35414314354750669263616981)
                    ·
                      refine ⟨830022992689468810866023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35414314354750669263616981 830022992689468810866023)
                      ·
                        rfl

theorem cell23_1616464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_1616464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616464 prefixEnd_1616464 := by exact prefixLift 1616464
  have htrace : WordTrace (prefixWord ++ tailWord_1616464) baseStart_1616464 baseEnd_1616464 := by
    simpa [prefixWord, tailWord_1616464, baseEnd_1616464] using wordTrace_append hprefix tailTrace_1616464
  have hstable : (prefixWord ++ tailWord_1616464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616464).length < 2 ^ (prefixWord ++ tailWord_1616464).sum := by decide
  have hdescent : baseEnd_1616464 < baseStart_1616464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616541 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_1616541 : Nat := 118140960795 + 1616541 * 2 ^ 59
def prefixEnd_1616541 : Nat := 4983230072969 + 3 ^ 40 * 1616541 * 2
def baseEnd_1616541 : Nat := 830062530699865009603169

theorem tailTrace_1616541 : CollatzResearch.WordTrace tailWord_1616541 prefixEnd_1616541 830062530699865009603169 := by
  unfold tailWord_1616541
  simp only [CollatzResearch.WordTrace]
  refine ⟨58960094036555515067801477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39306729357703676711867651 58960094036555515067801477)
  ·
    refine ⟨11055017631854159075212777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58960094036555515067801477 11055017631854159075212777)
    ·
      refine ⟨8291263223890619306409583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11055017631854159075212777 8291263223890619306409583)
      ·
        refine ⟨12436894835835928959614375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8291263223890619306409583 12436894835835928959614375)
        ·
          refine ⟨18655342253753893439421563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12436894835835928959614375 18655342253753893439421563)
          ·
            refine ⟨27983013380630840159132345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18655342253753893439421563 27983013380630840159132345)
            ·
              refine ⟨20987260035473130119349259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27983013380630840159132345 20987260035473130119349259)
              ·
                refine ⟨31480890053209695179023889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20987260035473130119349259 31480890053209695179023889)
                ·
                  refine ⟨23610667539907271384267917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31480890053209695179023889 23610667539907271384267917)
                  ·
                    refine ⟨8854000327465226769100469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23610667539907271384267917 8854000327465226769100469)
                    ·
                      refine ⟨830062530699865009603169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8854000327465226769100469 830062530699865009603169)
                      ·
                        rfl

theorem cell23_1616541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_1616541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616541 prefixEnd_1616541 := by exact prefixLift 1616541
  have htrace : WordTrace (prefixWord ++ tailWord_1616541) baseStart_1616541 baseEnd_1616541 := by
    simpa [prefixWord, tailWord_1616541, baseEnd_1616541] using wordTrace_append hprefix tailTrace_1616541
  have hstable : (prefixWord ++ tailWord_1616541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616541).length < 2 ^ (prefixWord ++ tailWord_1616541).sum := by decide
  have hdescent : baseEnd_1616541 < baseStart_1616541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616565 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 3, 4]
def baseStart_1616565 : Nat := 118140960795 + 1616565 * 2 ^ 59
def prefixEnd_1616565 : Nat := 4983230072969 + 3 ^ 40 * 1616565 * 2
def baseEnd_1616565 : Nat := 276691618078524305234353

theorem tailTrace_1616565 : CollatzResearch.WordTrace tailWord_1616565 prefixEnd_1616565 276691618078524305234353 := by
  unfold tailWord_1616565
  simp only [CollatzResearch.WordTrace]
  refine ⟨58960969388468567166675149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39307312925645711444450099 58960969388468567166675149)
  ·
    refine ⟨22110363520675712687503181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58960969388468567166675149 22110363520675712687503181)
    ·
      refine ⟨8291386320253392257813693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22110363520675712687503181 8291386320253392257813693)
      ·
        refine ⟨3109269870095022096680135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8291386320253392257813693 3109269870095022096680135)
        ·
          refine ⟨4663904805142533145020203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3109269870095022096680135 4663904805142533145020203)
          ·
            refine ⟨6995857207713799717530305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4663904805142533145020203 6995857207713799717530305)
            ·
              refine ⟨5246892905785349788147729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6995857207713799717530305 5246892905785349788147729)
              ·
                refine ⟨3935169679339012341110797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5246892905785349788147729 3935169679339012341110797)
                ·
                  refine ⟨1475688629752129627916549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3935169679339012341110797 1475688629752129627916549)
                  ·
                    refine ⟨276691618078524305234353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1475688629752129627916549 276691618078524305234353)
                    ·
                      rfl

theorem cell23_1616565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_1616565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616565 prefixEnd_1616565 := by exact prefixLift 1616565
  have htrace : WordTrace (prefixWord ++ tailWord_1616565) baseStart_1616565 baseEnd_1616565 := by
    simpa [prefixWord, tailWord_1616565, baseEnd_1616565] using wordTrace_append hprefix tailTrace_1616565
  have hstable : (prefixWord ++ tailWord_1616565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616565).length < 2 ^ (prefixWord ++ tailWord_1616565).sum := by decide
  have hdescent : baseEnd_1616565 < baseStart_1616565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616591 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 7, 5]
def baseStart_1616591 : Nat := 118140960795 + 1616591 * 2 ^ 59
def prefixEnd_1616591 : Nat := 4983230072969 + 3 ^ 40 * 1616591 * 2
def baseEnd_1616591 : Nat := 276696068244196604659313

theorem tailTrace_1616591 : CollatzResearch.WordTrace tailWord_1616591 prefixEnd_1616591 276696068244196604659313 := by
  unfold tailWord_1616591
  simp only [CollatzResearch.WordTrace]
  refine ⟨58961917686374373607121627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39307945124249582404747751 58961917686374373607121627)
  ·
    refine ⟨88442876529561560410682441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58961917686374373607121627 88442876529561560410682441)
    ·
      refine ⟨66332157397171170308011831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88442876529561560410682441 66332157397171170308011831)
      ·
        refine ⟨99498236095756755462017747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66332157397171170308011831 99498236095756755462017747)
        ·
          refine ⟨149247354143635133193026621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99498236095756755462017747 149247354143635133193026621)
          ·
            refine ⟨55967757803863174947384983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149247354143635133193026621 55967757803863174947384983)
            ·
              refine ⟨83951636705794762421077475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55967757803863174947384983 83951636705794762421077475)
              ·
                refine ⟨125927455058692143631616213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83951636705794762421077475 125927455058692143631616213)
                ·
                  refine ⟨2951424727938097116366005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 125927455058692143631616213 2951424727938097116366005)
                  ·
                    refine ⟨276696068244196604659313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2951424727938097116366005 276696068244196604659313)
                    ·
                      rfl

theorem cell23_1616591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 5].length) (baseStart_1616591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616591 prefixEnd_1616591 := by exact prefixLift 1616591
  have htrace : WordTrace (prefixWord ++ tailWord_1616591) baseStart_1616591 baseEnd_1616591 := by
    simpa [prefixWord, tailWord_1616591, baseEnd_1616591] using wordTrace_append hprefix tailTrace_1616591
  have hstable : (prefixWord ++ tailWord_1616591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616591).length < 2 ^ (prefixWord ++ tailWord_1616591).sum := by decide
  have hdescent : baseEnd_1616591 < baseStart_1616591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616655 : List Nat := [1, 1, 2, 1, 1, 1, 8, 2, 2, 4]
def baseStart_1616655 : Nat := 118140960795 + 1616655 * 2 ^ 59
def prefixEnd_1616655 : Nat := 4983230072969 + 3 ^ 40 * 1616655 * 2
def baseEnd_1616655 : Nat := 276707022498159187859215

theorem tailTrace_1616655 : CollatzResearch.WordTrace tailWord_1616655 prefixEnd_1616655 276707022498159187859215 := by
  unfold tailWord_1616655
  simp only [CollatzResearch.WordTrace]
  refine ⟨58964251958142512537451419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39309501305428341691634279 58964251958142512537451419)
  ·
    refine ⟨88446377937213768806177129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58964251958142512537451419 88446377937213768806177129)
    ·
      refine ⟨66334783452910326604632847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88446377937213768806177129 66334783452910326604632847)
      ·
        refine ⟨99502175179365489906949271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66334783452910326604632847 99502175179365489906949271)
        ·
          refine ⟨149253262769048234860423907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99502175179365489906949271 149253262769048234860423907)
          ·
            refine ⟨223879894153572352290635861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149253262769048234860423907 223879894153572352290635861)
            ·
              refine ⟨2623592509612176003405889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 223879894153572352290635861 2623592509612176003405889)
              ·
                refine ⟨1967694382209132002554417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2623592509612176003405889 1967694382209132002554417)
                ·
                  refine ⟨1475770786656849001915813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1967694382209132002554417 1475770786656849001915813)
                  ·
                    refine ⟨276707022498159187859215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1475770786656849001915813 276707022498159187859215)
                    ·
                      rfl

theorem cell23_1616655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 4].length) (baseStart_1616655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616655 prefixEnd_1616655 := by exact prefixLift 1616655
  have htrace : WordTrace (prefixWord ++ tailWord_1616655) baseStart_1616655 baseEnd_1616655 := by
    simpa [prefixWord, tailWord_1616655, baseEnd_1616655] using wordTrace_append hprefix tailTrace_1616655
  have hstable : (prefixWord ++ tailWord_1616655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616655).length < 2 ^ (prefixWord ++ tailWord_1616655).sum := by decide
  have hdescent : baseEnd_1616655 < baseStart_1616655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616668 : List Nat := [2, 2, 3, 1, 1, 3, 3, 8]
def baseStart_1616668 : Nat := 118140960795 + 1616668 * 2 ^ 59
def prefixEnd_1616668 : Nat := 4983230072969 + 3 ^ 40 * 1616668 * 2
def baseEnd_1616668 : Nat := 30745471953443926396855

theorem tailTrace_1616668 : CollatzResearch.WordTrace tailWord_1616668 prefixEnd_1616668 30745471953443926396855 := by
  unfold tailWord_1616668
  simp only [CollatzResearch.WordTrace]
  refine ⟨29482363053547707878837329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39309817404730277171783105 29482363053547707878837329)
  ·
    refine ⟨22111772290160780909127997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29482363053547707878837329 22111772290160780909127997)
    ·
      refine ⟨8291914608810292840922999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22111772290160780909127997 8291914608810292840922999)
      ·
        refine ⟨12437871913215439261384499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8291914608810292840922999 12437871913215439261384499)
        ·
          refine ⟨18656807869823158892076749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12437871913215439261384499 18656807869823158892076749)
          ·
            refine ⟨6996302951183684584528781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18656807869823158892076749 6996302951183684584528781)
            ·
              refine ⟨2623613606693881719198293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6996302951183684584528781 2623613606693881719198293)
              ·
                refine ⟨30745471953443926396855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2623613606693881719198293 30745471953443926396855)
                ·
                  rfl

theorem cell23_1616668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 8].length) (baseStart_1616668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616668 prefixEnd_1616668 := by exact prefixLift 1616668
  have htrace : WordTrace (prefixWord ++ tailWord_1616668) baseStart_1616668 baseEnd_1616668 := by
    simpa [prefixWord, tailWord_1616668, baseEnd_1616668] using wordTrace_append hprefix tailTrace_1616668
  have hstable : (prefixWord ++ tailWord_1616668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616668).length < 2 ^ (prefixWord ++ tailWord_1616668).sum := by decide
  have hdescent : baseEnd_1616668 < baseStart_1616668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616695 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 4, 1, 3]
def baseStart_1616695 : Nat := 118140960795 + 1616695 * 2 ^ 59
def prefixEnd_1616695 : Nat := 4983230072969 + 3 ^ 40 * 1616695 * 2
def baseEnd_1616695 : Nat := 830141606720657407077461

theorem tailTrace_1616695 : CollatzResearch.WordTrace tailWord_1616695 prefixEnd_1616695 830141606720657407077461 := by
  unfold tailWord_1616695
  simp only [CollatzResearch.WordTrace]
  refine ⟨58965710877997599368907539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39310473918665066245938359 58965710877997599368907539)
  ·
    refine ⟨88448566316996399053361309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58965710877997599368907539 88448566316996399053361309)
    ·
      refine ⟨33168212368873649645010491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88448566316996399053361309 33168212368873649645010491)
      ·
        refine ⟨49752318553310474467515737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33168212368873649645010491 49752318553310474467515737)
        ·
          refine ⟨37314238914982855850636803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49752318553310474467515737 37314238914982855850636803)
          ·
            refine ⟨55971358372474283775955205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37314238914982855850636803 55971358372474283775955205)
            ·
              refine ⟨10494629694838928207991601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55971358372474283775955205 10494629694838928207991601)
              ·
                refine ⟨7870972271129196155993701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10494629694838928207991601 7870972271129196155993701)
                ·
                  refine ⟨1475807300836724279248819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7870972271129196155993701 1475807300836724279248819)
                  ·
                    refine ⟨2213710951255086418873229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1475807300836724279248819 2213710951255086418873229)
                    ·
                      refine ⟨830141606720657407077461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2213710951255086418873229 830141606720657407077461)
                      ·
                        rfl

theorem cell23_1616695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 1, 3].length) (baseStart_1616695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616695 prefixEnd_1616695 := by exact prefixLift 1616695
  have htrace : WordTrace (prefixWord ++ tailWord_1616695) baseStart_1616695 baseEnd_1616695 := by
    simpa [prefixWord, tailWord_1616695, baseEnd_1616695] using wordTrace_append hprefix tailTrace_1616695
  have hstable : (prefixWord ++ tailWord_1616695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616695).length < 2 ^ (prefixWord ++ tailWord_1616695).sum := by decide
  have hdescent : baseEnd_1616695 < baseStart_1616695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616718 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_1616718 : Nat := 118140960795 + 1616718 * 2 ^ 59
def prefixEnd_1616718 : Nat := 4983230072969 + 3 ^ 40 * 1616718 * 2
def baseEnd_1616718 : Nat := 830153416775710817089855

theorem tailTrace_1616718 : CollatzResearch.WordTrace tailWord_1616718 prefixEnd_1616718 830153416775710817089855 := by
  unfold tailWord_1616718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7370818719614284287124351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39311033171276182864663205 7370818719614284287124351)
  ·
    refine ⟨11056228079421426430686527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7370818719614284287124351 11056228079421426430686527)
    ·
      refine ⟨16584342119132139646029791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11056228079421426430686527 16584342119132139646029791)
      ·
        refine ⟨24876513178698209469044687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16584342119132139646029791 24876513178698209469044687)
        ·
          refine ⟨37314769768047314203567031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24876513178698209469044687 37314769768047314203567031)
          ·
            refine ⟨55972154652070971305350547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37314769768047314203567031 55972154652070971305350547)
            ·
              refine ⟨83958231978106456958025821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55972154652070971305350547 83958231978106456958025821)
              ·
                refine ⟨31484336991789921359259683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83958231978106456958025821 31484336991789921359259683)
                ·
                  refine ⟨47226505487684882038889525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31484336991789921359259683 47226505487684882038889525)
                  ·
                    refine ⟨4427484889470457691145893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47226505487684882038889525 4427484889470457691145893)
                    ·
                      refine ⟨830153416775710817089855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4427484889470457691145893 830153416775710817089855)
                      ·
                        rfl

theorem cell23_1616718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_1616718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616718 prefixEnd_1616718 := by exact prefixLift 1616718
  have htrace : WordTrace (prefixWord ++ tailWord_1616718) baseStart_1616718 baseEnd_1616718 := by
    simpa [prefixWord, tailWord_1616718, baseEnd_1616718] using wordTrace_append hprefix tailTrace_1616718
  have hstable : (prefixWord ++ tailWord_1616718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616718).length < 2 ^ (prefixWord ++ tailWord_1616718).sum := by decide
  have hdescent : baseEnd_1616718 < baseStart_1616718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616729 : List Nat := [1, 2, 1, 2, 2, 5, 3, 1, 2, 1, 3]
def baseStart_1616729 : Nat := 118140960795 + 1616729 * 2 ^ 59
def prefixEnd_1616729 : Nat := 4983230072969 + 3 ^ 40 * 1616729 * 2
def baseEnd_1616729 : Nat := 830159065062910274052305

theorem tailTrace_1616729 : CollatzResearch.WordTrace tailWord_1616729 prefixEnd_1616729 830159065062910274052305 := by
  unfold tailWord_1616729
  simp only [CollatzResearch.WordTrace]
  refine ⟨58966950959874423175645241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39311300639916282117096827 58966950959874423175645241)
  ·
    refine ⟨44225213219905817381733931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58966950959874423175645241 44225213219905817381733931)
    ·
      refine ⟨66337819829858726072600897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44225213219905817381733931 66337819829858726072600897)
      ·
        refine ⟨49753364872394044554450673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66337819829858726072600897 49753364872394044554450673)
        ·
          refine ⟨37315023654295533415838005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49753364872394044554450673 37315023654295533415838005)
          ·
            refine ⟨3498283467590206257734813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37315023654295533415838005 3498283467590206257734813)
            ·
              refine ⟨1311856300346327346650555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3498283467590206257734813 1311856300346327346650555)
              ·
                refine ⟨1967784450519491019975833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311856300346327346650555 1967784450519491019975833)
                ·
                  refine ⟨1475838337889618264981875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1967784450519491019975833 1475838337889618264981875)
                  ·
                    refine ⟨2213757506834427397472813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1475838337889618264981875 2213757506834427397472813)
                    ·
                      refine ⟨830159065062910274052305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2213757506834427397472813 830159065062910274052305)
                      ·
                        rfl

theorem cell23_1616729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 2, 1, 3].length) (baseStart_1616729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616729 prefixEnd_1616729 := by exact prefixLift 1616729
  have htrace : WordTrace (prefixWord ++ tailWord_1616729) baseStart_1616729 baseEnd_1616729 := by
    simpa [prefixWord, tailWord_1616729, baseEnd_1616729] using wordTrace_append hprefix tailTrace_1616729
  have hstable : (prefixWord ++ tailWord_1616729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616729).length < 2 ^ (prefixWord ++ tailWord_1616729).sum := by decide
  have hdescent : baseEnd_1616729 < baseStart_1616729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616739 : List Nat := [1, 1, 1, 5, 3, 2, 2, 2, 1, 3, 2]
def baseStart_1616739 : Nat := 118140960795 + 1616739 * 2 ^ 59
def prefixEnd_1616739 : Nat := 4983230072969 + 3 ^ 40 * 1616739 * 2
def baseEnd_1616739 : Nat := 830164199869455234927259

theorem tailTrace_1616739 : CollatzResearch.WordTrace tailWord_1616739 prefixEnd_1616739 830164199869455234927259 := by
  unfold tailWord_1616739
  simp only [CollatzResearch.WordTrace]
  refine ⟨58967315689838194883509271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39311543793225463255672847 58967315689838194883509271)
  ·
    refine ⟨88450973534757292325263907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58967315689838194883509271 88450973534757292325263907)
    ·
      refine ⟨132676460302135938487895861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88450973534757292325263907 132676460302135938487895861)
      ·
        refine ⟨12438418153325244233240237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132676460302135938487895861 12438418153325244233240237)
        ·
          refine ⟨4664406807496966587465089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12438418153325244233240237 4664406807496966587465089)
          ·
            refine ⟨3498305105622724940598817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4664406807496966587465089 3498305105622724940598817)
            ·
              refine ⟨2623728829217043705449113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3498305105622724940598817 2623728829217043705449113)
              ·
                refine ⟨1967796621912782779086835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2623728829217043705449113 1967796621912782779086835)
                ·
                  refine ⟨2951694932869174168630253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1967796621912782779086835 2951694932869174168630253)
                  ·
                    refine ⟨1106885599825940313236345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2951694932869174168630253 1106885599825940313236345)
                    ·
                      refine ⟨830164199869455234927259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1106885599825940313236345 830164199869455234927259)
                      ·
                        rfl

theorem cell23_1616739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_1616739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616739 prefixEnd_1616739 := by exact prefixLift 1616739
  have htrace : WordTrace (prefixWord ++ tailWord_1616739) baseStart_1616739 baseEnd_1616739 := by
    simpa [prefixWord, tailWord_1616739, baseEnd_1616739] using wordTrace_append hprefix tailTrace_1616739
  have hstable : (prefixWord ++ tailWord_1616739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616739).length < 2 ^ (prefixWord ++ tailWord_1616739).sum := by decide
  have hdescent : baseEnd_1616739 < baseStart_1616739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616752 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 4, 2, 2]
def baseStart_1616752 : Nat := 118140960795 + 1616752 * 2 ^ 59
def prefixEnd_1616752 : Nat := 4983230072969 + 3 ^ 40 * 1616752 * 2
def baseEnd_1616752 : Nat := 830170875117963684064699

theorem tailTrace_1616752 : CollatzResearch.WordTrace tailWord_1616752 prefixEnd_1616752 830170875117963684064699 := by
  unfold tailWord_1616752
  simp only [CollatzResearch.WordTrace]
  refine ⟨29483894919395549051866255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39311859892527398735821673 29483894919395549051866255)
  ·
    refine ⟨44225842379093323577799383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29483894919395549051866255 44225842379093323577799383)
    ·
      refine ⟨66338763568639985366699075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44225842379093323577799383 66338763568639985366699075)
      ·
        refine ⟨99508145352959978050048613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66338763568639985366699075 99508145352959978050048613)
        ·
          refine ⟨18657777253679995884384115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99508145352959978050048613 18657777253679995884384115)
          ·
            refine ⟨27986665880519993826576173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18657777253679995884384115 27986665880519993826576173)
            ·
              refine ⟨10494999705194997684966065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27986665880519993826576173 10494999705194997684966065)
              ·
                refine ⟨7871249778896248263724549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10494999705194997684966065 7871249778896248263724549)
                ·
                  refine ⟨1475859333543046549448353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7871249778896248263724549 1475859333543046549448353)
                  ·
                    refine ⟨1106894500157284912086265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1475859333543046549448353 1106894500157284912086265)
                    ·
                      refine ⟨830170875117963684064699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1106894500157284912086265 830170875117963684064699)
                      ·
                        rfl

theorem cell23_1616752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 4, 2, 2].length) (baseStart_1616752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616752 prefixEnd_1616752 := by exact prefixLift 1616752
  have htrace : WordTrace (prefixWord ++ tailWord_1616752) baseStart_1616752 baseEnd_1616752 := by
    simpa [prefixWord, tailWord_1616752, baseEnd_1616752] using wordTrace_append hprefix tailTrace_1616752
  have hstable : (prefixWord ++ tailWord_1616752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616752).length < 2 ^ (prefixWord ++ tailWord_1616752).sum := by decide
  have hdescent : baseEnd_1616752 < baseStart_1616752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616775 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 7]
def baseStart_1616775 : Nat := 118140960795 + 1616775 * 2 ^ 59
def prefixEnd_1616775 : Nat := 4983230072969 + 3 ^ 40 * 1616775 * 2
def baseEnd_1616775 : Nat := 92242520574779677119677

theorem tailTrace_1616775 : CollatzResearch.WordTrace tailWord_1616775 prefixEnd_1616775 92242520574779677119677 := by
  unfold tailWord_1616775
  simp only [CollatzResearch.WordTrace]
  refine ⟨58968628717707773031819779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39312419145138515354546519 58968628717707773031819779)
  ·
    refine ⟨88452943076561659547729669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58968628717707773031819779 88452943076561659547729669)
    ·
      refine ⟨16584926826855311165199313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88452943076561659547729669 16584926826855311165199313)
      ·
        refine ⟨12438695120141483373899485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16584926826855311165199313 12438695120141483373899485)
        ·
          refine ⟨4664510670053056265212307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12438695120141483373899485 4664510670053056265212307)
          ·
            refine ⟨6996766005079584397818461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4664510670053056265212307 6996766005079584397818461)
            ·
              refine ⟨2623787251904844149181923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6996766005079584397818461 2623787251904844149181923)
              ·
                refine ⟨3935680877857266223772885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2623787251904844149181923 3935680877857266223772885)
                ·
                  refine ⟨92242520574779677119677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3935680877857266223772885 92242520574779677119677)
                  ·
                    rfl

theorem cell23_1616775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 7].length) (baseStart_1616775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616775 prefixEnd_1616775 := by exact prefixLift 1616775
  have htrace : WordTrace (prefixWord ++ tailWord_1616775) baseStart_1616775 baseEnd_1616775 := by
    simpa [prefixWord, tailWord_1616775, baseEnd_1616775] using wordTrace_append hprefix tailTrace_1616775
  have hstable : (prefixWord ++ tailWord_1616775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616775).length < 2 ^ (prefixWord ++ tailWord_1616775).sum := by decide
  have hdescent : baseEnd_1616775 < baseStart_1616775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616790 : List Nat := [5, 3, 1, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_1616790 : Nat := 118140960795 + 1616790 * 2 ^ 59
def prefixEnd_1616790 : Nat := 4983230072969 + 3 ^ 40 * 1616790 * 2
def baseEnd_1616790 : Nat := 830190387382834535389525

theorem tailTrace_1616790 : CollatzResearch.WordTrace tailWord_1616790 prefixEnd_1616790 830190387382834535389525 := by
  unfold tailWord_1616790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3685573488290839412100989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39312783875102287062410549 3685573488290839412100989)
  ·
    refine ⟨1382090058109064779537871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3685573488290839412100989 1382090058109064779537871)
    ·
      refine ⟨2073135087163597169306807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1382090058109064779537871 2073135087163597169306807)
      ·
        refine ⟨3109702630745395753960211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2073135087163597169306807 3109702630745395753960211)
        ·
          refine ⟨4664553946118093630940317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3109702630745395753960211 4664553946118093630940317)
          ·
            refine ⟨1749207729794285111602619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4664553946118093630940317 1749207729794285111602619)
            ·
              refine ⟨2623811594691427667403929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749207729794285111602619 2623811594691427667403929)
              ·
                refine ⟨1967858696018570750552947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2623811594691427667403929 1967858696018570750552947)
                ·
                  refine ⟨2951788044027856125829421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1967858696018570750552947 2951788044027856125829421)
                  ·
                    refine ⟨1106920516510446047186033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2951788044027856125829421 1106920516510446047186033)
                    ·
                      refine ⟨830190387382834535389525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1106920516510446047186033 830190387382834535389525)
                      ·
                        rfl

theorem cell23_1616790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_1616790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616790 prefixEnd_1616790 := by exact prefixLift 1616790
  have htrace : WordTrace (prefixWord ++ tailWord_1616790) baseStart_1616790 baseEnd_1616790 := by
    simpa [prefixWord, tailWord_1616790, baseEnd_1616790] using wordTrace_append hprefix tailTrace_1616790
  have hstable : (prefixWord ++ tailWord_1616790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616790).length < 2 ^ (prefixWord ++ tailWord_1616790).sum := by decide
  have hdescent : baseEnd_1616790 < baseStart_1616790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616848 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 10]
def baseStart_1616848 : Nat := 118140960795 + 1616848 * 2 ^ 59
def prefixEnd_1616848 : Nat := 4983230072969 + 3 ^ 40 * 1616848 * 2
def baseEnd_1616848 : Nat := 92246685473421700940473

theorem tailTrace_1616848 : CollatzResearch.WordTrace tailWord_1616848 prefixEnd_1616848 92246685473421700940473 := by
  unfold tailWord_1616848
  simp only [CollatzResearch.WordTrace]
  refine ⟨29485645623221653249613599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39314194164295537666151465 29485645623221653249613599)
  ·
    refine ⟨44228468434832479874420399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29485645623221653249613599 44228468434832479874420399)
    ·
      refine ⟨66342702652248719811630599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44228468434832479874420399 66342702652248719811630599)
      ·
        refine ⟨99514053978373079717445899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66342702652248719811630599 99514053978373079717445899)
        ·
          refine ⟨149271080967559619576168849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99514053978373079717445899 149271080967559619576168849)
          ·
            refine ⟨111953310725669714682126637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149271080967559619576168849 111953310725669714682126637)
            ·
              refine ⟨41982491522126143005797489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111953310725669714682126637 41982491522126143005797489)
              ·
                refine ⟨31486868641594607254348117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41982491522126143005797489 31486868641594607254348117)
                ·
                  refine ⟨92246685473421700940473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 31486868641594607254348117 92246685473421700940473)
                  ·
                    rfl

theorem cell23_1616848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 10].length) (baseStart_1616848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616848 prefixEnd_1616848 := by exact prefixLift 1616848
  have htrace : WordTrace (prefixWord ++ tailWord_1616848) baseStart_1616848 baseEnd_1616848 := by
    simpa [prefixWord, tailWord_1616848, baseEnd_1616848] using wordTrace_append hprefix tailTrace_1616848
  have hstable : (prefixWord ++ tailWord_1616848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616848).length < 2 ^ (prefixWord ++ tailWord_1616848).sum := by decide
  have hdescent : baseEnd_1616848 < baseStart_1616848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616852 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_1616852 : Nat := 118140960795 + 1616852 * 2 ^ 59
def prefixEnd_1616852 : Nat := 4983230072969 + 3 ^ 40 * 1616852 * 2
def baseEnd_1616852 : Nat := 276740741061137764271413

theorem tailTrace_1616852 : CollatzResearch.WordTrace tailWord_1616852 prefixEnd_1616852 276740741061137764271413 := by
  unfold tailWord_1616852
  simp only [CollatzResearch.WordTrace]
  refine ⟨29485718569214407591186405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39314291425619210121581873 29485718569214407591186405)
  ·
    refine ⟨5528572231727701423347451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29485718569214407591186405 5528572231727701423347451)
    ·
      refine ⟨8292858347591552135021177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5528572231727701423347451 8292858347591552135021177)
      ·
        refine ⟨6219643760693664101265883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8292858347591552135021177 6219643760693664101265883)
        ·
          refine ⟨9329465641040496151898825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6219643760693664101265883 9329465641040496151898825)
          ·
            refine ⟨6997099230780372113924119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9329465641040496151898825 6997099230780372113924119)
            ·
              refine ⟨10495648846170558170886179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6997099230780372113924119 10495648846170558170886179)
              ·
                refine ⟨15743473269255837256329269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10495648846170558170886179 15743473269255837256329269)
                ·
                  refine ⟨1475950618992734742780869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15743473269255837256329269 1475950618992734742780869)
                  ·
                    refine ⟨276740741061137764271413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1475950618992734742780869 276740741061137764271413)
                    ·
                      rfl

theorem cell23_1616852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_1616852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616852 prefixEnd_1616852 := by exact prefixLift 1616852
  have htrace : WordTrace (prefixWord ++ tailWord_1616852) baseStart_1616852 baseEnd_1616852 := by
    simpa [prefixWord, tailWord_1616852, baseEnd_1616852] using wordTrace_append hprefix tailTrace_1616852
  have hstable : (prefixWord ++ tailWord_1616852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616852).length < 2 ^ (prefixWord ++ tailWord_1616852).sum := by decide
  have hdescent : baseEnd_1616852 < baseStart_1616852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616886 : List Nat := [5, 1, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_1616886 : Nat := 118140960795 + 1616886 * 2 ^ 59
def prefixEnd_1616886 : Nat := 4983230072969 + 3 ^ 40 * 1616886 * 2
def baseEnd_1616886 : Nat := 276746560508555386596361

theorem tailTrace_1616886 : CollatzResearch.WordTrace tailWord_1616886 prefixEnd_1616886 276746560508555386596361 := by
  unfold tailWord_1616886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3685792326269102436819407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39315118146870425992740341 3685792326269102436819407)
  ·
    refine ⟨5528688489403653655229111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3685792326269102436819407 5528688489403653655229111)
    ·
      refine ⟨8293032734105480482843667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5528688489403653655229111 8293032734105480482843667)
      ·
        refine ⟨12439549101158220724265501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8293032734105480482843667 12439549101158220724265501)
        ·
          refine ⟨4664830912934332771599563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12439549101158220724265501 4664830912934332771599563)
          ·
            refine ⟨6997246369401499157399345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4664830912934332771599563 6997246369401499157399345)
            ·
              refine ⟨5247934777051124368049509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6997246369401499157399345 5247934777051124368049509)
              ·
                refine ⟨983987770697085819009283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5247934777051124368049509 983987770697085819009283)
                ·
                  refine ⟨1475981656045628728513925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 983987770697085819009283 1475981656045628728513925)
                  ·
                    refine ⟨276746560508555386596361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1475981656045628728513925 276746560508555386596361)
                    ·
                      rfl

theorem cell23_1616886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_1616886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616886 prefixEnd_1616886 := by exact prefixLift 1616886
  have htrace : WordTrace (prefixWord ++ tailWord_1616886) baseStart_1616886 baseEnd_1616886 := by
    simpa [prefixWord, tailWord_1616886, baseEnd_1616886] using wordTrace_append hprefix tailTrace_1616886
  have hstable : (prefixWord ++ tailWord_1616886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616886).length < 2 ^ (prefixWord ++ tailWord_1616886).sum := by decide
  have hdescent : baseEnd_1616886 < baseStart_1616886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616919 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 1, 5, 2]
def baseStart_1616919 : Nat := 118140960795 + 1616919 * 2 ^ 59
def prefixEnd_1616919 : Nat := 4983230072969 + 3 ^ 40 * 1616919 * 2
def baseEnd_1616919 : Nat := 830256626387264530676431

theorem tailTrace_1616919 : CollatzResearch.WordTrace tailWord_1616919 prefixEnd_1616919 830256626387264530676431 := by
  unfold tailWord_1616919
  simp only [CollatzResearch.WordTrace]
  refine ⟨58973880829186085625061811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39315920552790723750041207 58973880829186085625061811)
  ·
    refine ⟨88460821243779128437592717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58973880829186085625061811 88460821243779128437592717)
    ·
      refine ⟨33172807966417173164097269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88460821243779128437592717 33172807966417173164097269)
      ·
        refine ⟨3109950746851609984134119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33172807966417173164097269 3109950746851609984134119)
        ·
          refine ⟨4664926120277414976201179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3109950746851609984134119 4664926120277414976201179)
          ·
            refine ⟨6997389180416122464301769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4664926120277414976201179 6997389180416122464301769)
            ·
              refine ⟨5248041885312091848226327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6997389180416122464301769 5248041885312091848226327)
              ·
                refine ⟨7872062827968137772339491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5248041885312091848226327 7872062827968137772339491)
                ·
                  refine ⟨11808094241952206658509237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7872062827968137772339491 11808094241952206658509237)
                  ·
                    refine ⟨1107008835183019374235241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11808094241952206658509237 1107008835183019374235241)
                    ·
                      refine ⟨830256626387264530676431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1107008835183019374235241 830256626387264530676431)
                      ·
                        rfl

theorem cell23_1616919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_1616919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616919 prefixEnd_1616919 := by exact prefixLift 1616919
  have htrace : WordTrace (prefixWord ++ tailWord_1616919) baseStart_1616919 baseEnd_1616919 := by
    simpa [prefixWord, tailWord_1616919, baseEnd_1616919] using wordTrace_append hprefix tailTrace_1616919
  have hstable : (prefixWord ++ tailWord_1616919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616919).length < 2 ^ (prefixWord ++ tailWord_1616919).sum := by decide
  have hdescent : baseEnd_1616919 < baseStart_1616919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616945 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 3, 1, 6]
def baseStart_1616945 : Nat := 118140960795 + 1616945 * 2 ^ 59
def prefixEnd_1616945 : Nat := 4983230072969 + 3 ^ 40 * 1616945 * 2
def baseEnd_1616945 : Nat := 830269976884281428951311

theorem tailTrace_1616945 : CollatzResearch.WordTrace tailWord_1616945 prefixEnd_1616945 830269976884281428951311 := by
  unfold tailWord_1616945
  simp only [CollatzResearch.WordTrace]
  refine ⟨58974829127091892065508289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39316552751394594710338859 58974829127091892065508289)
  ·
    refine ⟨44231121845318919049131217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58974829127091892065508289 44231121845318919049131217)
    ·
      refine ⟨33173341383989189286848413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44231121845318919049131217 33173341383989189286848413)
      ·
        refine ⟨12440003018995945982568155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33173341383989189286848413 12440003018995945982568155)
        ·
          refine ⟨18660004528493918973852233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12440003018995945982568155 18660004528493918973852233)
          ·
            refine ⟨13995003396370439230389175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18660004528493918973852233 13995003396370439230389175)
            ·
              refine ⟨20992505094555658845583763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13995003396370439230389175 20992505094555658845583763)
              ·
                refine ⟨31488757641833488268375645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20992505094555658845583763 31488757641833488268375645)
                ·
                  refine ⟨11808284115687558100640867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31488757641833488268375645 11808284115687558100640867)
                  ·
                    refine ⟨17712426173531337150961301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11808284115687558100640867 17712426173531337150961301)
                    ·
                      refine ⟨830269976884281428951311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17712426173531337150961301 830269976884281428951311)
                      ·
                        rfl

theorem cell23_1616945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_1616945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616945 prefixEnd_1616945 := by exact prefixLift 1616945
  have htrace : WordTrace (prefixWord ++ tailWord_1616945) baseStart_1616945 baseEnd_1616945 := by
    simpa [prefixWord, tailWord_1616945, baseEnd_1616945] using wordTrace_append hprefix tailTrace_1616945
  have hstable : (prefixWord ++ tailWord_1616945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616945).length < 2 ^ (prefixWord ++ tailWord_1616945).sum := by decide
  have hdescent : baseEnd_1616945 < baseStart_1616945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616952 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 1, 1, 5]
def baseStart_1616952 : Nat := 118140960795 + 1616952 * 2 ^ 59
def prefixEnd_1616952 : Nat := 4983230072969 + 3 ^ 40 * 1616952 * 2
def baseEnd_1616952 : Nat := 830273571248862901563779

theorem tailTrace_1616952 : CollatzResearch.WordTrace tailWord_1616952 prefixEnd_1616952 830273571248862901563779 := by
  unfold tailWord_1616952
  simp only [CollatzResearch.WordTrace]
  refine ⟨29487542219033266130506555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39316722958711021507342073 29487542219033266130506555)
  ·
    refine ⟨44231313328549899195759833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29487542219033266130506555 44231313328549899195759833)
    ·
      refine ⟨33173484996412424396819875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44231313328549899195759833 33173484996412424396819875)
      ·
        refine ⟨49760227494618636595229813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33173484996412424396819875 49760227494618636595229813)
        ·
          refine ⟨4665021327620497180802795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49760227494618636595229813 4665021327620497180802795)
          ·
            refine ⟨6997531991430745771204193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4665021327620497180802795 6997531991430745771204193)
            ·
              refine ⟨5248148993573059328403145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6997531991430745771204193 5248148993573059328403145)
              ·
                refine ⟨3936111745179794496302359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5248148993573059328403145 3936111745179794496302359)
                ·
                  refine ⟨5904167617769691744453539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3936111745179794496302359 5904167617769691744453539)
                  ·
                    refine ⟨8856251426654537616680309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5904167617769691744453539 8856251426654537616680309)
                    ·
                      refine ⟨830273571248862901563779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8856251426654537616680309 830273571248862901563779)
                      ·
                        rfl

theorem cell23_1616952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_1616952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616952 prefixEnd_1616952 := by exact prefixLift 1616952
  have htrace : WordTrace (prefixWord ++ tailWord_1616952) baseStart_1616952 baseEnd_1616952 := by
    simpa [prefixWord, tailWord_1616952, baseEnd_1616952] using wordTrace_append hprefix tailTrace_1616952
  have hstable : (prefixWord ++ tailWord_1616952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616952).length < 2 ^ (prefixWord ++ tailWord_1616952).sum := by decide
  have hdescent : baseEnd_1616952 < baseStart_1616952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616966 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_1616966 : Nat := 118140960795 + 1616966 * 2 ^ 59
def prefixEnd_1616966 : Nat := 4983230072969 + 3 ^ 40 * 1616966 * 2
def baseEnd_1616966 : Nat := 830280759978025846788715

theorem tailTrace_1616966 : CollatzResearch.WordTrace tailWord_1616966 prefixEnd_1616966 830280759978025846788715 := by
  unfold tailWord_1616966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1842987345625494145375711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39317063373343875101348501 1842987345625494145375711)
  ·
    refine ⟨2764481018438241218063567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1842987345625494145375711 2764481018438241218063567)
    ·
      refine ⟨4146721527657361827095351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2764481018438241218063567 4146721527657361827095351)
      ·
        refine ⟨6220082291486042740643027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4146721527657361827095351 6220082291486042740643027)
        ·
          refine ⟨9330123437229064110964541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6220082291486042740643027 9330123437229064110964541)
          ·
            refine ⟨3498796288960899041611703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9330123437229064110964541 3498796288960899041611703)
            ·
              refine ⟨5248194433441348562417555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3498796288960899041611703 5248194433441348562417555)
              ·
                refine ⟨7872291650162022843626333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5248194433441348562417555 7872291650162022843626333)
                ·
                  refine ⟨2952109368810758566359875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7872291650162022843626333 2952109368810758566359875)
                  ·
                    refine ⟨4428164053216137849539813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2952109368810758566359875 4428164053216137849539813)
                    ·
                      refine ⟨830280759978025846788715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4428164053216137849539813 830280759978025846788715)
                      ·
                        rfl

theorem cell23_1616966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_1616966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616966 prefixEnd_1616966 := by exact prefixLift 1616966
  have htrace : WordTrace (prefixWord ++ tailWord_1616966) baseStart_1616966 baseEnd_1616966 := by
    simpa [prefixWord, tailWord_1616966, baseEnd_1616966] using wordTrace_append hprefix tailTrace_1616966
  have hstable : (prefixWord ++ tailWord_1616966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616966).length < 2 ^ (prefixWord ++ tailWord_1616966).sum := by decide
  have hdescent : baseEnd_1616966 < baseStart_1616966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616989 : List Nat := [1, 4, 4, 1, 3, 10]
def baseStart_1616989 : Nat := 118140960795 + 1616989 * 2 ^ 59
def prefixEnd_1616989 : Nat := 4983230072969 + 3 ^ 40 * 1616989 * 2
def baseEnd_1616989 : Nat := 3416841851987980480663

theorem tailTrace_1616989 : CollatzResearch.WordTrace tailWord_1616989 prefixEnd_1616989 3416841851987980480663 := by
  unfold tailWord_1616989
  simp only [CollatzResearch.WordTrace]
  refine ⟨58976433938932487580110021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39317622625954991720073347 58976433938932487580110021)
  ·
    refine ⟨11058081363549841421270629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58976433938932487580110021 11058081363549841421270629)
    ·
      refine ⟨2073390255665595266488243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11058081363549841421270629 2073390255665595266488243)
      ·
        refine ⟨3110085383498392899732365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2073390255665595266488243 3110085383498392899732365)
        ·
          refine ⟨1166282018811897337399637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3110085383498392899732365 1166282018811897337399637)
          ·
            refine ⟨3416841851987980480663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1166282018811897337399637 3416841851987980480663)
            ·
              rfl

theorem cell23_1616989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 10].length) (baseStart_1616989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1616989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1616989 prefixEnd_1616989 := by exact prefixLift 1616989
  have htrace : WordTrace (prefixWord ++ tailWord_1616989) baseStart_1616989 baseEnd_1616989 := by
    simpa [prefixWord, tailWord_1616989, baseEnd_1616989] using wordTrace_append hprefix tailTrace_1616989
  have hstable : (prefixWord ++ tailWord_1616989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616989).length < 2 ^ (prefixWord ++ tailWord_1616989).sum := by decide
  have hdescent : baseEnd_1616989 < baseStart_1616989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617002 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 2, 7]
def baseStart_1617002 : Nat := 118140960795 + 1617002 * 2 ^ 59
def prefixEnd_1617002 : Nat := 4983230072969 + 3 ^ 40 * 1617002 * 2
def baseEnd_1617002 : Nat := 276766415093862568646183

theorem tailTrace_1617002 : CollatzResearch.WordTrace tailWord_1617002 prefixEnd_1617002 276766415093862568646183 := by
  unfold tailWord_1617002
  simp only [CollatzResearch.WordTrace]
  refine ⟨14744227021971347700083315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39317938725256927200222173 14744227021971347700083315)
  ·
    refine ⟨22116340532957021550124973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14744227021971347700083315 22116340532957021550124973)
    ·
      refine ⟨8293627699858883081296865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22116340532957021550124973 8293627699858883081296865)
      ·
        refine ⟨6220220774894162310972649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8293627699858883081296865 6220220774894162310972649)
        ·
          refine ⟨4665165581170621733229487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6220220774894162310972649 4665165581170621733229487)
          ·
            refine ⟨6997748371755932599844231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4665165581170621733229487 6997748371755932599844231)
            ·
              refine ⟨10496622557633898899766347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6997748371755932599844231 10496622557633898899766347)
              ·
                refine ⟨15744933836450848349649521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10496622557633898899766347 15744933836450848349649521)
                ·
                  refine ⟨11808700377338136262237141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15744933836450848349649521 11808700377338136262237141)
                  ·
                    refine ⟨276766415093862568646183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11808700377338136262237141 276766415093862568646183)
                    ·
                      rfl

theorem cell23_1617002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_1617002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617002 prefixEnd_1617002 := by exact prefixLift 1617002
  have htrace : WordTrace (prefixWord ++ tailWord_1617002) baseStart_1617002 baseEnd_1617002 := by
    simpa [prefixWord, tailWord_1617002, baseEnd_1617002] using wordTrace_append hprefix tailTrace_1617002
  have hstable : (prefixWord ++ tailWord_1617002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617002).length < 2 ^ (prefixWord ++ tailWord_1617002).sum := by decide
  have hdescent : baseEnd_1617002 < baseStart_1617002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617056 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 4, 2, 2]
def baseStart_1617056 : Nat := 118140960795 + 1617056 * 2 ^ 59
def prefixEnd_1617056 : Nat := 4983230072969 + 3 ^ 40 * 1617056 * 2
def baseEnd_1617056 : Nat := 830326973236930494663301

theorem tailTrace_1617056 : CollatzResearch.WordTrace tailWord_1617056 prefixEnd_1617056 830326973236930494663301 := by
  unfold tailWord_1617056
  simp only [CollatzResearch.WordTrace]
  refine ⟨29489438814844879011399511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39319251753126505348532681 29489438814844879011399511)
  ·
    refine ⟨44234158222267318517099267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29489438814844879011399511 44234158222267318517099267)
    ·
      refine ⟨66351237333400977775648901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44234158222267318517099267 66351237333400977775648901)
      ·
        refine ⟨12440857000012683332934169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66351237333400977775648901 12440857000012683332934169)
        ·
          refine ⟨9330642750009512499700627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12440857000012683332934169 9330642750009512499700627)
          ·
            refine ⟨13995964125014268749550941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9330642750009512499700627 13995964125014268749550941)
            ·
              refine ⟨5248486546880350781081603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13995964125014268749550941 5248486546880350781081603)
              ·
                refine ⟨7872729820320526171622405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5248486546880350781081603 7872729820320526171622405)
                ·
                  refine ⟨1476136841310098657179201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7872729820320526171622405 1476136841310098657179201)
                  ·
                    refine ⟨1107102630982573992884401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1476136841310098657179201 1107102630982573992884401)
                    ·
                      refine ⟨830326973236930494663301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1107102630982573992884401 830326973236930494663301)
                      ·
                        rfl

theorem cell23_1617056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_1617056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617056 prefixEnd_1617056 := by exact prefixLift 1617056
  have htrace : WordTrace (prefixWord ++ tailWord_1617056) baseStart_1617056 baseEnd_1617056 := by
    simpa [prefixWord, tailWord_1617056, baseEnd_1617056] using wordTrace_append hprefix tailTrace_1617056
  have hstable : (prefixWord ++ tailWord_1617056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617056).length < 2 ^ (prefixWord ++ tailWord_1617056).sum := by decide
  have hdescent : baseEnd_1617056 < baseStart_1617056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617073 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 1, 4, 2]
def baseStart_1617073 : Nat := 118140960795 + 1617073 * 2 ^ 59
def prefixEnd_1617073 : Nat := 4983230072969 + 3 ^ 40 * 1617073 * 2
def baseEnd_1617073 : Nat := 830335702408056928150723

theorem tailTrace_1617073 : CollatzResearch.WordTrace tailWord_1617073 prefixEnd_1617073 830335702408056928150723 := by
  unfold tailWord_1617073
  simp only [CollatzResearch.WordTrace]
  refine ⟨58979497670628169926167873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39319665113752113284111915 58979497670628169926167873)
  ·
    refine ⟨44234623252971127444625905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58979497670628169926167873 44234623252971127444625905)
    ·
      refine ⟨33175967439728345583469429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44234623252971127444625905 33175967439728345583469429)
      ·
        refine ⟨3110246947474532398450259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33175967439728345583469429 3110246947474532398450259)
        ·
          refine ⟨4665370421211798597675389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3110246947474532398450259 4665370421211798597675389)
          ·
            refine ⟨1749513907954424474128271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4665370421211798597675389 1749513907954424474128271)
            ·
              refine ⟨2624270861931636711192407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749513907954424474128271 2624270861931636711192407)
              ·
                refine ⟨3936406292897455066788611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2624270861931636711192407 3936406292897455066788611)
                ·
                  refine ⟨5904609439346182600182917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3936406292897455066788611 5904609439346182600182917)
                  ·
                    refine ⟨1107114269877409237534297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5904609439346182600182917 1107114269877409237534297)
                    ·
                      refine ⟨830335702408056928150723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1107114269877409237534297 830335702408056928150723)
                      ·
                        rfl

theorem cell23_1617073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_1617073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617073 prefixEnd_1617073 := by exact prefixLift 1617073
  have htrace : WordTrace (prefixWord ++ tailWord_1617073) baseStart_1617073 baseEnd_1617073 := by
    simpa [prefixWord, tailWord_1617073, baseEnd_1617073] using wordTrace_append hprefix tailTrace_1617073
  have hstable : (prefixWord ++ tailWord_1617073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617073).length < 2 ^ (prefixWord ++ tailWord_1617073).sum := by decide
  have hdescent : baseEnd_1617073 < baseStart_1617073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617109 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 4, 5]
def baseStart_1617109 : Nat := 118140960795 + 1617109 * 2 ^ 59
def prefixEnd_1617109 : Nat := 4983230072969 + 3 ^ 40 * 1617109 * 2
def baseEnd_1617109 : Nat := 276784729237206262433519

theorem tailTrace_1617109 : CollatzResearch.WordTrace tailWord_1617109 prefixEnd_1617109 276784729237206262433519 := by
  unfold tailWord_1617109
  simp only [CollatzResearch.WordTrace]
  refine ⟨58980810698497748074478381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39320540465665165382985587 58980810698497748074478381)
  ·
    refine ⟨22117804011936655527929393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58980810698497748074478381 22117804011936655527929393)
    ·
      refine ⟨16588353008952491645947045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22117804011936655527929393 16588353008952491645947045)
      ·
        refine ⟨3110316189178592183615071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16588353008952491645947045 3110316189178592183615071)
        ·
          refine ⟨4665474283767888275422607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3110316189178592183615071 4665474283767888275422607)
          ·
            refine ⟨6998211425651832413133911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4665474283767888275422607 6998211425651832413133911)
            ·
              refine ⟨10497317138477748619700867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6998211425651832413133911 10497317138477748619700867)
              ·
                refine ⟨15745975707716622929551301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10497317138477748619700867 15745975707716622929551301)
                ·
                  refine ⟨2952370445196866799290869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15745975707716622929551301 2952370445196866799290869)
                  ·
                    refine ⟨276784729237206262433519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2952370445196866799290869 276784729237206262433519)
                    ·
                      rfl

theorem cell23_1617109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_1617109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617109 prefixEnd_1617109 := by exact prefixLift 1617109
  have htrace : WordTrace (prefixWord ++ tailWord_1617109) baseStart_1617109 baseEnd_1617109 := by
    simpa [prefixWord, tailWord_1617109, baseEnd_1617109] using wordTrace_append hprefix tailTrace_1617109
  have hstable : (prefixWord ++ tailWord_1617109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617109).length < 2 ^ (prefixWord ++ tailWord_1617109).sum := by decide
  have hdescent : baseEnd_1617109 < baseStart_1617109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617166 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3]
def baseStart_1617166 : Nat := 118140960795 + 1617166 * 2 ^ 59
def prefixEnd_1617166 : Nat := 4983230072969 + 3 ^ 40 * 1617166 * 2
def baseEnd_1617166 : Nat := 830383456108925064287795

theorem tailTrace_1617166 : CollatzResearch.WordTrace tailWord_1617166 prefixEnd_1617166 830383456108925064287795 := by
  unfold tailWord_1617166
  simp only [CollatzResearch.WordTrace]
  refine ⟨7372861207411405851162919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39321926439527497872868901 7372861207411405851162919)
  ·
    refine ⟨11059291811117108776744379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7372861207411405851162919 11059291811117108776744379)
    ·
      refine ⟨16588937716675663165116569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11059291811117108776744379 16588937716675663165116569)
      ·
        refine ⟨12441703287506747373837427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16588937716675663165116569 12441703287506747373837427)
        ·
          refine ⟨18662554931260121060756141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12441703287506747373837427 18662554931260121060756141)
          ·
            refine ⟨6998458099222545397783553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18662554931260121060756141 6998458099222545397783553)
            ·
              refine ⟨5248843574416909048337665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6998458099222545397783553 5248843574416909048337665)
              ·
                refine ⟨3936632680812681786253249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5248843574416909048337665 3936632680812681786253249)
                ·
                  refine ⟨2952474510609511339689937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3936632680812681786253249 2952474510609511339689937)
                  ·
                    refine ⟨2214355882957133504767453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2952474510609511339689937 2214355882957133504767453)
                    ·
                      refine ⟨830383456108925064287795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2214355882957133504767453 830383456108925064287795)
                      ·
                        rfl

theorem cell23_1617166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_1617166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617166 prefixEnd_1617166 := by exact prefixLift 1617166
  have htrace : WordTrace (prefixWord ++ tailWord_1617166) baseStart_1617166 baseEnd_1617166 := by
    simpa [prefixWord, tailWord_1617166, baseEnd_1617166] using wordTrace_append hprefix tailTrace_1617166
  have hstable : (prefixWord ++ tailWord_1617166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617166).length < 2 ^ (prefixWord ++ tailWord_1617166).sum := by decide
  have hdescent : baseEnd_1617166 < baseStart_1617166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617169 : List Nat := [1, 2, 2, 1, 1, 4, 4, 2, 6]
def baseStart_1617169 : Nat := 118140960795 + 1617169 * 2 ^ 59
def prefixEnd_1617169 : Nat := 4983230072969 + 3 ^ 40 * 1617169 * 2
def baseEnd_1617169 : Nat := 92264999616765394727809

theorem tailTrace_1617169 : CollatzResearch.WordTrace tailWord_1617169 prefixEnd_1617169 92264999616765394727809 := by
  unfold tailWord_1617169
  simp only [CollatzResearch.WordTrace]
  refine ⟨58982999078280378321662561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39321999385520252214441707 58982999078280378321662561)
  ·
    refine ⟨44237249308710283741246921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58982999078280378321662561 44237249308710283741246921)
    ·
      refine ⟨33177936981532712805935191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44237249308710283741246921 33177936981532712805935191)
      ·
        refine ⟨49766905472299069208902787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33177936981532712805935191 49766905472299069208902787)
        ·
          refine ⟨74650358208448603813354181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49766905472299069208902787 74650358208448603813354181)
          ·
            refine ⟨13996942164084113215003909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74650358208448603813354181 13996942164084113215003909)
            ·
              refine ⟨2624426655765771227813233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13996942164084113215003909 2624426655765771227813233)
              ·
                refine ⟨1968319991824328420859925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2624426655765771227813233 1968319991824328420859925)
                ·
                  refine ⟨92264999616765394727809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1968319991824328420859925 92264999616765394727809)
                  ·
                    rfl

theorem cell23_1617169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 6].length) (baseStart_1617169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617169 prefixEnd_1617169 := by exact prefixLift 1617169
  have htrace : WordTrace (prefixWord ++ tailWord_1617169) baseStart_1617169 baseEnd_1617169 := by
    simpa [prefixWord, tailWord_1617169, baseEnd_1617169] using wordTrace_append hprefix tailTrace_1617169
  have hstable : (prefixWord ++ tailWord_1617169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617169).length < 2 ^ (prefixWord ++ tailWord_1617169).sum := by decide
  have hdescent : baseEnd_1617169 < baseStart_1617169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617199 : List Nat := [1, 1, 2, 1, 2, 1, 3, 6, 1, 5]
def baseStart_1617199 : Nat := 118140960795 + 1617199 * 2 ^ 59
def prefixEnd_1617199 : Nat := 4983230072969 + 3 ^ 40 * 1617199 * 2
def baseEnd_1617199 : Nat := 276800133656841145058381

theorem tailTrace_1617199 : CollatzResearch.WordTrace tailWord_1617199 prefixEnd_1617199 276800133656841145058381 := by
  unfold tailWord_1617199
  simp only [CollatzResearch.WordTrace]
  refine ⟨58984093268171693445254651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39322728845447795630169767 58984093268171693445254651)
  ·
    refine ⟨88476139902257540167881977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58984093268171693445254651 88476139902257540167881977)
    ·
      refine ⟨66357104926693155125911483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88476139902257540167881977 66357104926693155125911483)
      ·
        refine ⟨99535657390039732688867225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66357104926693155125911483 99535657390039732688867225)
        ·
          refine ⟨74651743042529799516650419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99535657390039732688867225 74651743042529799516650419)
          ·
            refine ⟨111977614563794699274975629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74651743042529799516650419 111977614563794699274975629)
            ·
              refine ⟨41991605461423012228115861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111977614563794699274975629 41991605461423012228115861)
              ·
                refine ⟨1968356506004203698192931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41991605461423012228115861 1968356506004203698192931)
                ·
                  refine ⟨2952534759006305547289397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1968356506004203698192931 2952534759006305547289397)
                  ·
                    refine ⟨276800133656841145058381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2952534759006305547289397 276800133656841145058381)
                    ·
                      rfl

theorem cell23_1617199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 5].length) (baseStart_1617199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617199 prefixEnd_1617199 := by exact prefixLift 1617199
  have htrace : WordTrace (prefixWord ++ tailWord_1617199) baseStart_1617199 baseEnd_1617199 := by
    simpa [prefixWord, tailWord_1617199, baseEnd_1617199] using wordTrace_append hprefix tailTrace_1617199
  have hstable : (prefixWord ++ tailWord_1617199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617199).length < 2 ^ (prefixWord ++ tailWord_1617199).sum := by decide
  have hdescent : baseEnd_1617199 < baseStart_1617199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617239 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 5]
def baseStart_1617239 : Nat := 118140960795 + 1617239 * 2 ^ 59
def prefixEnd_1617239 : Nat := 4983230072969 + 3 ^ 40 * 1617239 * 2
def baseEnd_1617239 : Nat := 830420940196703278674959

theorem tailTrace_1617239 : CollatzResearch.WordTrace tailWord_1617239 prefixEnd_1617239 830420940196703278674959 := by
  unfold tailWord_1617239
  simp only [CollatzResearch.WordTrace]
  refine ⟨58985552188026780276710771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39323701458684520184473847 58985552188026780276710771)
  ·
    refine ⟨88478328282040170415066157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58985552188026780276710771 88478328282040170415066157)
    ·
      refine ⟨33179373105765063905649809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88478328282040170415066157 33179373105765063905649809)
      ·
        refine ⟨24884529829323797929237357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33179373105765063905649809 24884529829323797929237357)
        ·
          refine ⟨9331698685996424223464009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24884529829323797929237357 9331698685996424223464009)
          ·
            refine ⟨6998774014497318167598007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9331698685996424223464009 6998774014497318167598007)
            ·
              refine ⟨10498161021745977251397011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6998774014497318167598007 10498161021745977251397011)
              ·
                refine ⟨15747241532618965877095517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10498161021745977251397011 15747241532618965877095517)
                ·
                  refine ⟨5905215574732112203910819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15747241532618965877095517 5905215574732112203910819)
                  ·
                    refine ⟨8857823362098168305866229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5905215574732112203910819 8857823362098168305866229)
                    ·
                      refine ⟨830420940196703278674959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8857823362098168305866229 830420940196703278674959)
                      ·
                        rfl

theorem cell23_1617239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_1617239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617239 prefixEnd_1617239 := by exact prefixLift 1617239
  have htrace : WordTrace (prefixWord ++ tailWord_1617239) baseStart_1617239 baseEnd_1617239 := by
    simpa [prefixWord, tailWord_1617239, baseEnd_1617239] using wordTrace_append hprefix tailTrace_1617239
  have hstable : (prefixWord ++ tailWord_1617239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617239).length < 2 ^ (prefixWord ++ tailWord_1617239).sum := by decide
  have hdescent : baseEnd_1617239 < baseStart_1617239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617253 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 3, 2, 2]
def baseStart_1617253 : Nat := 118140960795 + 1617253 * 2 ^ 59
def prefixEnd_1617253 : Nat := 4983230072969 + 3 ^ 40 * 1617253 * 2
def baseEnd_1617253 : Nat := 830428128925866223899895

theorem tailTrace_1617253 : CollatzResearch.WordTrace tailWord_1617253 prefixEnd_1617253 830428128925866223899895 := by
  unfold tailWord_1617253
  simp only [CollatzResearch.WordTrace]
  refine ⟨58986062809976060667720413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39324041873317373778480275 58986062809976060667720413)
  ·
    refine ⟨22119773553741022750395155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58986062809976060667720413 22119773553741022750395155)
    ·
      refine ⟨33179660330611534125592733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22119773553741022750395155 33179660330611534125592733)
      ·
        refine ⟨12442372623979325297097275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33179660330611534125592733 12442372623979325297097275)
        ·
          refine ⟨18663558935968987945645913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12442372623979325297097275 18663558935968987945645913)
          ·
            refine ⟨13997669201976740959234435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18663558935968987945645913 13997669201976740959234435)
            ·
              refine ⟨20996503802965111438851653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13997669201976740959234435 20996503802965111438851653)
              ·
                refine ⟨3936844463055958394784685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20996503802965111438851653 3936844463055958394784685)
                ·
                  refine ⟨1476316673645984398044257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3936844463055958394784685 1476316673645984398044257)
                  ·
                    refine ⟨1107237505234488298533193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1476316673645984398044257 1107237505234488298533193)
                    ·
                      refine ⟨830428128925866223899895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1107237505234488298533193 830428128925866223899895)
                      ·
                        rfl

theorem cell23_1617253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_1617253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617253 prefixEnd_1617253 := by exact prefixLift 1617253
  have htrace : WordTrace (prefixWord ++ tailWord_1617253) baseStart_1617253 baseEnd_1617253 := by
    simpa [prefixWord, tailWord_1617253, baseEnd_1617253] using wordTrace_append hprefix tailTrace_1617253
  have hstable : (prefixWord ++ tailWord_1617253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617253).length < 2 ^ (prefixWord ++ tailWord_1617253).sum := by decide
  have hdescent : baseEnd_1617253 < baseStart_1617253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617320 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1617320 : Nat := 118140960795 + 1617320 * 2 ^ 59
def prefixEnd_1617320 : Nat := 4983230072969 + 3 ^ 40 * 1617320 * 2
def baseEnd_1617320 : Nat := 830462532129717461762087

theorem tailTrace_1617320 : CollatzResearch.WordTrace tailWord_1617320 prefixEnd_1617320 830462532129717461762087 := by
  unfold tailWord_1617320
  simp only [CollatzResearch.WordTrace]
  refine ⟨29494253250366665555204707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39325671000488887406939609 29494253250366665555204707)
  ·
    refine ⟨44241379875549998332807061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29494253250366665555204707 44241379875549998332807061)
    ·
      refine ⟨2073814681666406171850331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44241379875549998332807061 2073814681666406171850331)
      ·
        refine ⟨3110722022499609257775497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2073814681666406171850331 3110722022499609257775497)
        ·
          refine ⟨2333041516874706943331623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3110722022499609257775497 2333041516874706943331623)
          ·
            refine ⟨3499562275312060414997435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2333041516874706943331623 3499562275312060414997435)
            ·
              refine ⟨5249343412968090622496153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3499562275312060414997435 5249343412968090622496153)
              ·
                refine ⟨3937007559726067966872115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5249343412968090622496153 3937007559726067966872115)
                ·
                  refine ⟨5905511339589101950308173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3937007559726067966872115 5905511339589101950308173)
                  ·
                    refine ⟨2214566752345913231365565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5905511339589101950308173 2214566752345913231365565)
                    ·
                      refine ⟨830462532129717461762087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2214566752345913231365565 830462532129717461762087)
                      ·
                        rfl

theorem cell23_1617320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1617320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617320 prefixEnd_1617320 := by exact prefixLift 1617320
  have htrace : WordTrace (prefixWord ++ tailWord_1617320) baseStart_1617320 baseEnd_1617320 := by
    simpa [prefixWord, tailWord_1617320, baseEnd_1617320] using wordTrace_append hprefix tailTrace_1617320
  have hstable : (prefixWord ++ tailWord_1617320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617320).length < 2 ^ (prefixWord ++ tailWord_1617320).sum := by decide
  have hdescent : baseEnd_1617320 < baseStart_1617320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617343 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 4, 2, 2]
def baseStart_1617343 : Nat := 118140960795 + 1617343 * 2 ^ 59
def prefixEnd_1617343 : Nat := 4983230072969 + 3 ^ 40 * 1617343 * 2
def baseEnd_1617343 : Nat := 830474342184770871774481

theorem tailTrace_1617343 : CollatzResearch.WordTrace tailWord_1617343 prefixEnd_1617343 830474342184770871774481 := by
  unfold tailWord_1617343
  simp only [CollatzResearch.WordTrace]
  refine ⟨58989345379650006038496683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39326230253100004025664455 58989345379650006038496683)
  ·
    refine ⟨88484018069475009057745025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58989345379650006038496683 88484018069475009057745025)
    ·
      refine ⟨66363013552106256793308769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88484018069475009057745025 66363013552106256793308769)
      ·
        refine ⟨49772260164079692594981577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66363013552106256793308769 49772260164079692594981577)
        ·
          refine ⟨37329195123059769446236183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49772260164079692594981577 37329195123059769446236183)
          ·
            refine ⟨55993792684589654169354275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37329195123059769446236183 55993792684589654169354275)
            ·
              refine ⟨83990689026884481254031413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55993792684589654169354275 83990689026884481254031413)
              ·
                refine ⟨7874127096270420117565445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83990689026884481254031413 7874127096270420117565445)
                ·
                  refine ⟨1476398830550703772043521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7874127096270420117565445 1476398830550703772043521)
                  ·
                    refine ⟨1107299122913027829032641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1476398830550703772043521 1107299122913027829032641)
                    ·
                      refine ⟨830474342184770871774481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1107299122913027829032641 830474342184770871774481)
                      ·
                        rfl

theorem cell23_1617343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 2, 2].length) (baseStart_1617343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617343 prefixEnd_1617343 := by exact prefixLift 1617343
  have htrace : WordTrace (prefixWord ++ tailWord_1617343) baseStart_1617343 baseEnd_1617343 := by
    simpa [prefixWord, tailWord_1617343, baseEnd_1617343] using wordTrace_append hprefix tailTrace_1617343
  have hstable : (prefixWord ++ tailWord_1617343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617343).length < 2 ^ (prefixWord ++ tailWord_1617343).sum := by decide
  have hdescent : baseEnd_1617343 < baseStart_1617343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617356 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1617356 : Nat := 118140960795 + 1617356 * 2 ^ 59
def prefixEnd_1617356 : Nat := 4983230072969 + 3 ^ 40 * 1617356 * 2
def baseEnd_1617356 : Nat := 830481017433279320911921

theorem tailTrace_1617356 : CollatzResearch.WordTrace tailWord_1617356 prefixEnd_1617356 830481017433279320911921 := by
  unfold tailWord_1617356
  simp only [CollatzResearch.WordTrace]
  refine ⟨29494909764301454629359961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39326546352401939505813281 29494909764301454629359961)
  ·
    refine ⟨22121182323226090972019971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29494909764301454629359961 22121182323226090972019971)
    ·
      refine ⟨33181773484839136458029957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22121182323226090972019971 33181773484839136458029957)
      ·
        refine ⟨6221582528407338085880617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33181773484839136458029957 6221582528407338085880617)
        ·
          refine ⟨4666186896305503564410463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6221582528407338085880617 4666186896305503564410463)
          ·
            refine ⟨6999280344458255346615695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4666186896305503564410463 6999280344458255346615695)
            ·
              refine ⟨10498920516687383019923543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6999280344458255346615695 10498920516687383019923543)
              ·
                refine ⟨15748380775031074529885315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10498920516687383019923543 15748380775031074529885315)
                ·
                  refine ⟨23622571162546611794827973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15748380775031074529885315 23622571162546611794827973)
                  ·
                    refine ⟨4429232092977489711530245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23622571162546611794827973 4429232092977489711530245)
                    ·
                      refine ⟨830481017433279320911921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4429232092977489711530245 830481017433279320911921)
                      ·
                        rfl

theorem cell23_1617356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1617356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617356 prefixEnd_1617356 := by exact prefixLift 1617356
  have htrace : WordTrace (prefixWord ++ tailWord_1617356) baseStart_1617356 baseEnd_1617356 := by
    simpa [prefixWord, tailWord_1617356, baseEnd_1617356] using wordTrace_append hprefix tailTrace_1617356
  have hstable : (prefixWord ++ tailWord_1617356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617356).length < 2 ^ (prefixWord ++ tailWord_1617356).sum := by decide
  have hdescent : baseEnd_1617356 < baseStart_1617356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617383 : List Nat := [1, 1, 5, 2, 1, 2, 1, 5, 5]
def baseStart_1617383 : Nat := 118140960795 + 1617383 * 2 ^ 59
def prefixEnd_1617383 : Nat := 4983230072969 + 3 ^ 40 * 1617383 * 2
def baseEnd_1617383 : Nat := 92277209045661190586033

theorem tailTrace_1617383 : CollatzResearch.WordTrace tailWord_1617383 prefixEnd_1617383 92277209045661190586033 := by
  unfold tailWord_1617383
  simp only [CollatzResearch.WordTrace]
  refine ⟨58990804299505092869952803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39327202866336728579968535 58990804299505092869952803)
  ·
    refine ⟨88486206449257639304929205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58990804299505092869952803 88486206449257639304929205)
    ·
      refine ⟨8295581854617903684837113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88486206449257639304929205 8295581854617903684837113)
      ·
        refine ⟨6221686390963427763627835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8295581854617903684837113 6221686390963427763627835)
        ·
          refine ⟨9332529586445141645441753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6221686390963427763627835 9332529586445141645441753)
          ·
            refine ⟨6999397189833856234081315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9332529586445141645441753 6999397189833856234081315)
            ·
              refine ⟨10499095784750784351121973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6999397189833856234081315 10499095784750784351121973)
              ·
                refine ⟨984290229820386032917685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10499095784750784351121973 984290229820386032917685)
                ·
                  refine ⟨92277209045661190586033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 984290229820386032917685 92277209045661190586033)
                  ·
                    rfl

theorem cell23_1617383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 5].length) (baseStart_1617383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617383 prefixEnd_1617383 := by exact prefixLift 1617383
  have htrace : WordTrace (prefixWord ++ tailWord_1617383) baseStart_1617383 baseEnd_1617383 := by
    simpa [prefixWord, tailWord_1617383, baseEnd_1617383] using wordTrace_append hprefix tailTrace_1617383
  have hstable : (prefixWord ++ tailWord_1617383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617383).length < 2 ^ (prefixWord ++ tailWord_1617383).sum := by decide
  have hdescent : baseEnd_1617383 < baseStart_1617383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617394 : List Nat := [3, 2, 1, 4, 1, 3, 1, 2, 2, 2, 2]
def baseStart_1617394 : Nat := 118140960795 + 1617394 * 2 ^ 59
def prefixEnd_1617394 : Nat := 4983230072969 + 3 ^ 40 * 1617394 * 2
def baseEnd_1617394 : Nat := 830500529698150172236747

theorem tailTrace_1617394 : CollatzResearch.WordTrace tailWord_1617394 prefixEnd_1617394 830500529698150172236747 := by
  unfold tailWord_1617394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14747801375616310437150809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39327470334976827832402157 14747801375616310437150809)
  ·
    refine ⟨11060851031712232827863107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14747801375616310437150809 11060851031712232827863107)
    ·
      refine ⟨16591276547568349241794661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11060851031712232827863107 16591276547568349241794661)
      ·
        refine ⟨3110864352669065482836499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16591276547568349241794661 3110864352669065482836499)
        ·
          refine ⟨4666296529003598224254749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3110864352669065482836499 4666296529003598224254749)
          ·
            refine ⟨1749861198376349334095531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4666296529003598224254749 1749861198376349334095531)
            ·
              refine ⟨2624791797564524001143297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749861198376349334095531 2624791797564524001143297)
              ·
                refine ⟨1968593848173393000857473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2624791797564524001143297 1968593848173393000857473)
                ·
                  refine ⟨1476445386130044750643105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1968593848173393000857473 1476445386130044750643105)
                  ·
                    refine ⟨1107334039597533562982329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1476445386130044750643105 1107334039597533562982329)
                    ·
                      refine ⟨830500529698150172236747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1107334039597533562982329 830500529698150172236747)
                      ·
                        rfl

theorem cell23_1617394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_1617394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617394 prefixEnd_1617394 := by exact prefixLift 1617394
  have htrace : WordTrace (prefixWord ++ tailWord_1617394) baseStart_1617394 baseEnd_1617394 := by
    simpa [prefixWord, tailWord_1617394, baseEnd_1617394] using wordTrace_append hprefix tailTrace_1617394
  have hstable : (prefixWord ++ tailWord_1617394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617394).length < 2 ^ (prefixWord ++ tailWord_1617394).sum := by decide
  have hdescent : baseEnd_1617394 < baseStart_1617394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617410 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1617410 : Nat := 118140960795 + 1617410 * 2 ^ 59
def prefixEnd_1617410 : Nat := 4983230072969 + 3 ^ 40 * 1617410 * 2
def baseEnd_1617410 : Nat := 830508745388622109636673

theorem tailTrace_1617410 : CollatzResearch.WordTrace tailWord_1617410 prefixEnd_1617410 830508745388622109636673 := by
  unfold tailWord_1617410
  simp only [CollatzResearch.WordTrace]
  refine ⟨14747947267601819120296421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39327859380271517654123789 14747947267601819120296421)
  ·
    refine ⟨2765240112675341085055579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14747947267601819120296421 2765240112675341085055579)
    ·
      refine ⟨4147860169013011627583369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2765240112675341085055579 4147860169013011627583369)
      ·
        refine ⟨3110895126759758720687527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4147860169013011627583369 3110895126759758720687527)
        ·
          refine ⟨4666342690139638081031291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3110895126759758720687527 4666342690139638081031291)
          ·
            refine ⟨6999514035209457121546937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4666342690139638081031291 6999514035209457121546937)
            ·
              refine ⟨5249635526407092841160203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6999514035209457121546937 5249635526407092841160203)
              ·
                refine ⟨7874453289610639261740305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5249635526407092841160203 7874453289610639261740305)
                ·
                  refine ⟨5905839967207979446305229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7874453289610639261740305 5905839967207979446305229)
                  ·
                    refine ⟨2214689987702992292364461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5905839967207979446305229 2214689987702992292364461)
                    ·
                      refine ⟨830508745388622109636673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2214689987702992292364461 830508745388622109636673)
                      ·
                        rfl

theorem cell23_1617410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1617410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617410 prefixEnd_1617410 := by exact prefixLift 1617410
  have htrace : WordTrace (prefixWord ++ tailWord_1617410) baseStart_1617410 baseEnd_1617410 := by
    simpa [prefixWord, tailWord_1617410, baseEnd_1617410] using wordTrace_append hprefix tailTrace_1617410
  have hstable : (prefixWord ++ tailWord_1617410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617410).length < 2 ^ (prefixWord ++ tailWord_1617410).sum := by decide
  have hdescent : baseEnd_1617410 < baseStart_1617410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617416 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_1617416 : Nat := 118140960795 + 1617416 * 2 ^ 59
def prefixEnd_1617416 : Nat := 4983230072969 + 3 ^ 40 * 1617416 * 2
def baseEnd_1617416 : Nat := 830511826272549086161645

theorem tailTrace_1617416 : CollatzResearch.WordTrace tailWord_1617416 prefixEnd_1617416 830511826272549086161645 := by
  unfold tailWord_1617416
  simp only [CollatzResearch.WordTrace]
  refine ⟨29496003954192769752952051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39328005272257026337269401 29496003954192769752952051)
  ·
    refine ⟨44244005931289154629428077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29496003954192769752952051 44244005931289154629428077)
    ·
      refine ⟨16591502224233432986035529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44244005931289154629428077 16591502224233432986035529)
      ·
        refine ⟨12443626668175074739526647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16591502224233432986035529 12443626668175074739526647)
        ·
          refine ⟨18665440002262612109289971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12443626668175074739526647 18665440002262612109289971)
          ·
            refine ⟨27998160003393918163934957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18665440002262612109289971 27998160003393918163934957)
            ·
              refine ⟨10499310001272719311475609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27998160003393918163934957 10499310001272719311475609)
              ·
                refine ⟨7874482500954539483606707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10499310001272719311475609 7874482500954539483606707)
                ·
                  refine ⟨11811723751431809225410061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7874482500954539483606707 11811723751431809225410061)
                  ·
                    refine ⟨4429396406786928459528773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11811723751431809225410061 4429396406786928459528773)
                    ·
                      refine ⟨830511826272549086161645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4429396406786928459528773 830511826272549086161645)
                      ·
                        rfl

theorem cell23_1617416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_1617416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617416 prefixEnd_1617416 := by exact prefixLift 1617416
  have htrace : WordTrace (prefixWord ++ tailWord_1617416) baseStart_1617416 baseEnd_1617416 := by
    simpa [prefixWord, tailWord_1617416, baseEnd_1617416] using wordTrace_append hprefix tailTrace_1617416
  have hstable : (prefixWord ++ tailWord_1617416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617416).length < 2 ^ (prefixWord ++ tailWord_1617416).sum := by decide
  have hdescent : baseEnd_1617416 < baseStart_1617416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617456 : List Nat := [2, 1, 1, 1, 2, 3, 1, 6, 6]
def baseStart_1617456 : Nat := 118140960795 + 1617456 * 2 ^ 59
def prefixEnd_1617456 : Nat := 4983230072969 + 3 ^ 40 * 1617456 * 2
def baseEnd_1617456 : Nat := 92281373944303214406829

theorem tailTrace_1617456 : CollatzResearch.WordTrace tailWord_1617456 prefixEnd_1617456 92281373944303214406829 := by
  unfold tailWord_1617456
  simp only [CollatzResearch.WordTrace]
  refine ⟨29496733414120313168680111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39328977885493750891573481 29496733414120313168680111)
  ·
    refine ⟨44245100121180469753020167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29496733414120313168680111 44245100121180469753020167)
    ·
      refine ⟨66367650181770704629530251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44245100121180469753020167 66367650181770704629530251)
      ·
        refine ⟨99551475272656056944295377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66367650181770704629530251 99551475272656056944295377)
        ·
          refine ⟨74663606454492042708221533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99551475272656056944295377 74663606454492042708221533)
          ·
            refine ⟨27998852420434516015583075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74663606454492042708221533 27998852420434516015583075)
            ·
              refine ⟨41998278630651774023374613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27998852420434516015583075 41998278630651774023374613)
              ·
                refine ⟨1968669310811801907345685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41998278630651774023374613 1968669310811801907345685)
                ·
                  refine ⟨92281373944303214406829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1968669310811801907345685 92281373944303214406829)
                  ·
                    rfl

theorem cell23_1617456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 6].length) (baseStart_1617456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617456 prefixEnd_1617456 := by exact prefixLift 1617456
  have htrace : WordTrace (prefixWord ++ tailWord_1617456) baseStart_1617456 baseEnd_1617456 := by
    simpa [prefixWord, tailWord_1617456, baseEnd_1617456] using wordTrace_append hprefix tailTrace_1617456
  have hstable : (prefixWord ++ tailWord_1617456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617456).length < 2 ^ (prefixWord ++ tailWord_1617456).sum := by decide
  have hdescent : baseEnd_1617456 < baseStart_1617456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617473 : List Nat := [1, 2, 5, 1, 1, 1, 3, 3, 6]
def baseStart_1617473 : Nat := 118140960795 + 1617473 * 2 ^ 59
def prefixEnd_1617473 : Nat := 4983230072969 + 3 ^ 40 * 1617473 * 2
def baseEnd_1617473 : Nat := 92282343852206151460987

theorem tailTrace_1617473 : CollatzResearch.WordTrace tailWord_1617473 prefixEnd_1617473 92282343852206151460987 := by
  unfold tailWord_1617473
  simp only [CollatzResearch.WordTrace]
  refine ⟨58994086869179038240729073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39329391246119358827152715 58994086869179038240729073)
  ·
    refine ⟨44245565151884278680546805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58994086869179038240729073 44245565151884278680546805)
    ·
      refine ⟨4148021732989151126301263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44245565151884278680546805 4148021732989151126301263)
      ·
        refine ⟨6222032599483726689451895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4148021732989151126301263 6222032599483726689451895)
        ·
          refine ⟨9333048899225590034177843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6222032599483726689451895 9333048899225590034177843)
          ·
            refine ⟨13999573348838385051266765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9333048899225590034177843 13999573348838385051266765)
            ·
              refine ⟨5249840005814394394225037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13999573348838385051266765 5249840005814394394225037)
              ·
                refine ⟨1968690002180397897834389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5249840005814394394225037 1968690002180397897834389)
                ·
                  refine ⟨92282343852206151460987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1968690002180397897834389 92282343852206151460987)
                  ·
                    rfl

theorem cell23_1617473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 6].length) (baseStart_1617473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617473 prefixEnd_1617473 := by exact prefixLift 1617473
  have htrace : WordTrace (prefixWord ++ tailWord_1617473) baseStart_1617473 baseEnd_1617473 := by
    simpa [prefixWord, tailWord_1617473, baseEnd_1617473] using wordTrace_append hprefix tailTrace_1617473
  have hstable : (prefixWord ++ tailWord_1617473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617473).length < 2 ^ (prefixWord ++ tailWord_1617473).sum := by decide
  have hdescent : baseEnd_1617473 < baseStart_1617473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617483 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 5, 1, 3]
def baseStart_1617483 : Nat := 118140960795 + 1617483 * 2 ^ 59
def prefixEnd_1617483 : Nat := 4983230072969 + 3 ^ 40 * 1617483 * 2
def baseEnd_1617483 : Nat := 830546229476400324023837

theorem tailTrace_1617483 : CollatzResearch.WordTrace tailWord_1617483 prefixEnd_1617483 830546229476400324023837 := by
  unfold tailWord_1617483
  simp only [CollatzResearch.WordTrace]
  refine ⟨58994451599142809948593103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39329634399428539965728735 58994451599142809948593103)
  ·
    refine ⟨88491677398714214922889655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58994451599142809948593103 88491677398714214922889655)
    ·
      refine ⟨132737516098071322384334483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88491677398714214922889655 132737516098071322384334483)
      ·
        refine ⟨199106274147106983576501725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132737516098071322384334483 199106274147106983576501725)
        ·
          refine ⟨74664852805165118841188147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199106274147106983576501725 74664852805165118841188147)
          ·
            refine ⟨111997279207747678261782221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74664852805165118841188147 111997279207747678261782221)
            ·
              refine ⟨41998979702905379348168333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111997279207747678261782221 41998979702905379348168333)
              ·
                refine ⟨15749617388589517255563125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41998979702905379348168333 15749617388589517255563125)
                ·
                  refine ⟨1476526630180267242709043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15749617388589517255563125 1476526630180267242709043)
                  ·
                    refine ⟨2214789945270400864063565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1476526630180267242709043 2214789945270400864063565)
                    ·
                      refine ⟨830546229476400324023837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2214789945270400864063565 830546229476400324023837)
                      ·
                        rfl

theorem cell23_1617483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 1, 3].length) (baseStart_1617483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617483 prefixEnd_1617483 := by exact prefixLift 1617483
  have htrace : WordTrace (prefixWord ++ tailWord_1617483) baseStart_1617483 baseEnd_1617483 := by
    simpa [prefixWord, tailWord_1617483, baseEnd_1617483] using wordTrace_append hprefix tailTrace_1617483
  have hstable : (prefixWord ++ tailWord_1617483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617483).length < 2 ^ (prefixWord ++ tailWord_1617483).sum := by decide
  have hdescent : baseEnd_1617483 < baseStart_1617483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617516 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 5, 6]
def baseStart_1617516 : Nat := 118140960795 + 1617516 * 2 ^ 59
def prefixEnd_1617516 : Nat := 4983230072969 + 3 ^ 40 * 1617516 * 2
def baseEnd_1617516 : Nat := 276854391445999564970395

theorem tailTrace_1617516 : CollatzResearch.WordTrace tailWord_1617516 prefixEnd_1617516 276854391445999564970395 := by
  unfold tailWord_1617516
  simp only [CollatzResearch.WordTrace]
  refine ⟨29497827604011628292272201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39330436805348837723029601 29497827604011628292272201)
  ·
    refine ⟨22123370703008721219204151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29497827604011628292272201 22123370703008721219204151)
    ·
      refine ⟨33185056054513081828806227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22123370703008721219204151 33185056054513081828806227)
      ·
        refine ⟨49777584081769622743209341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33185056054513081828806227 49777584081769622743209341)
        ·
          refine ⟨18666594030663608528703503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49777584081769622743209341 18666594030663608528703503)
          ·
            refine ⟨27999891045995412793055255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18666594030663608528703503 27999891045995412793055255)
            ·
              refine ⟨41999836568993119189582883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27999891045995412793055255 41999836568993119189582883)
              ·
                refine ⟨62999754853489678784374325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41999836568993119189582883 62999754853489678784374325)
                ·
                  refine ⟨5906227017514657386035093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62999754853489678784374325 5906227017514657386035093)
                  ·
                    refine ⟨276854391445999564970395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5906227017514657386035093 276854391445999564970395)
                    ·
                      rfl

theorem cell23_1617516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_1617516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617516 prefixEnd_1617516 := by exact prefixLift 1617516
  have htrace : WordTrace (prefixWord ++ tailWord_1617516) baseStart_1617516 baseEnd_1617516 := by
    simpa [prefixWord, tailWord_1617516, baseEnd_1617516] using wordTrace_append hprefix tailTrace_1617516
  have hstable : (prefixWord ++ tailWord_1617516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617516).length < 2 ^ (prefixWord ++ tailWord_1617516).sum := by decide
  have hdescent : baseEnd_1617516 < baseStart_1617516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617533 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 1, 6]
def baseStart_1617533 : Nat := 118140960795 + 1617533 * 2 ^ 59
def prefixEnd_1617533 : Nat := 4983230072969 + 3 ^ 40 * 1617533 * 2
def baseEnd_1617533 : Nat := 276857301169708376132869

theorem tailTrace_1617533 : CollatzResearch.WordTrace tailWord_1617533 prefixEnd_1617533 276857301169708376132869 := by
  unfold tailWord_1617533
  simp only [CollatzResearch.WordTrace]
  refine ⟨58996275248961668487913253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39330850165974445658608835 58996275248961668487913253)
  ·
    refine ⟨11061801609180312841483735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58996275248961668487913253 11061801609180312841483735)
    ·
      refine ⟨16592702413770469262225603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11061801609180312841483735 16592702413770469262225603)
      ·
        refine ⟨24889053620655703893338405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16592702413770469262225603 24889053620655703893338405)
        ·
          refine ⟨4666697553872944480000951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24889053620655703893338405 4666697553872944480000951)
          ·
            refine ⟨7000046330809416720001427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4666697553872944480000951 7000046330809416720001427)
            ·
              refine ⟨10500069496214125080002141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7000046330809416720001427 10500069496214125080002141)
              ·
                refine ⟨3937526061080296905000803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10500069496214125080002141 3937526061080296905000803)
                ·
                  refine ⟨5906289091620445357501205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3937526061080296905000803 5906289091620445357501205)
                  ·
                    refine ⟨276857301169708376132869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5906289091620445357501205 276857301169708376132869)
                    ·
                      rfl

theorem cell23_1617533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_1617533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617533 prefixEnd_1617533 := by exact prefixLift 1617533
  have htrace : WordTrace (prefixWord ++ tailWord_1617533) baseStart_1617533 baseEnd_1617533 := by
    simpa [prefixWord, tailWord_1617533, baseEnd_1617533] using wordTrace_append hprefix tailTrace_1617533
  have hstable : (prefixWord ++ tailWord_1617533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617533).length < 2 ^ (prefixWord ++ tailWord_1617533).sum := by decide
  have hdescent : baseEnd_1617533 < baseStart_1617533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617554 : List Nat := [3, 2, 3, 1, 3, 2, 2, 1, 1, 5]
def baseStart_1617554 : Nat := 118140960795 + 1617554 * 2 ^ 59
def prefixEnd_1617554 : Nat := 4983230072969 + 3 ^ 40 * 1617554 * 2
def baseEnd_1617554 : Nat := 276860895534289848745337

theorem tailTrace_1617554 : CollatzResearch.WordTrace tailWord_1617554 prefixEnd_1617554 276860895534289848745337 := by
  unfold tailWord_1617554
  simp only [CollatzResearch.WordTrace]
  refine ⟨14749260295471397268606929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39331360787923726049618477 14749260295471397268606929)
  ·
    refine ⟨11061945221603547951455197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14749260295471397268606929 11061945221603547951455197)
    ·
      refine ⟨4148229458101330481795699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11061945221603547951455197 4148229458101330481795699)
      ·
        refine ⟨6222344187151995722693549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4148229458101330481795699 6222344187151995722693549)
        ·
          refine ⟨2333379070181998396010081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6222344187151995722693549 2333379070181998396010081)
          ·
            refine ⟨1750034302636498797007561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2333379070181998396010081 1750034302636498797007561)
            ·
              refine ⟨1312525726977374097755671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1750034302636498797007561 1312525726977374097755671)
              ·
                refine ⟨1968788590466061146633507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1312525726977374097755671 1968788590466061146633507)
                ·
                  refine ⟨2953182885699091719950261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1968788590466061146633507 2953182885699091719950261)
                  ·
                    refine ⟨276860895534289848745337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2953182885699091719950261 276860895534289848745337)
                    ·
                      rfl

theorem cell23_1617554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_1617554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617554 prefixEnd_1617554 := by exact prefixLift 1617554
  have htrace : WordTrace (prefixWord ++ tailWord_1617554) baseStart_1617554 baseEnd_1617554 := by
    simpa [prefixWord, tailWord_1617554, baseEnd_1617554] using wordTrace_append hprefix tailTrace_1617554
  have hstable : (prefixWord ++ tailWord_1617554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617554).length < 2 ^ (prefixWord ++ tailWord_1617554).sum := by decide
  have hdescent : baseEnd_1617554 < baseStart_1617554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617567 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 4, 4]
def baseStart_1617567 : Nat := 118140960795 + 1617567 * 2 ^ 59
def prefixEnd_1617567 : Nat := 4983230072969 + 3 ^ 40 * 1617567 * 2
def baseEnd_1617567 : Nat := 276863120617125998457817

theorem tailTrace_1617567 : CollatzResearch.WordTrace tailWord_1617567 prefixEnd_1617567 276863120617125998457817 := by
  unfold tailWord_1617567
  simp only [CollatzResearch.WordTrace]
  refine ⟨58997515330838492294650955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39331676887225661529767303 58997515330838492294650955)
  ·
    refine ⟨88496272996257738441976433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58997515330838492294650955 88496272996257738441976433)
    ·
      refine ⟨66372204747193303831482325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88496272996257738441976433 66372204747193303831482325)
      ·
        refine ⟨1555598548762343058550367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 66372204747193303831482325 1555598548762343058550367)
        ·
          refine ⟨2333397823143514587825551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1555598548762343058550367 2333397823143514587825551)
          ·
            refine ⟨3500096734715271881738327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2333397823143514587825551 3500096734715271881738327)
            ·
              refine ⟨5250145102072907822607491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3500096734715271881738327 5250145102072907822607491)
              ·
                refine ⟨7875217653109361733911237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5250145102072907822607491 7875217653109361733911237)
                ·
                  refine ⟨1476603309958005325108357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7875217653109361733911237 1476603309958005325108357)
                  ·
                    refine ⟨276863120617125998457817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1476603309958005325108357 276863120617125998457817)
                    ·
                      rfl

theorem cell23_1617567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 4].length) (baseStart_1617567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617567 prefixEnd_1617567 := by exact prefixLift 1617567
  have htrace : WordTrace (prefixWord ++ tailWord_1617567) baseStart_1617567 baseEnd_1617567 := by
    simpa [prefixWord, tailWord_1617567, baseEnd_1617567] using wordTrace_append hprefix tailTrace_1617567
  have hstable : (prefixWord ++ tailWord_1617567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617567).length < 2 ^ (prefixWord ++ tailWord_1617567).sum := by decide
  have hdescent : baseEnd_1617567 < baseStart_1617567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617573 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 3, 3, 3]
def baseStart_1617573 : Nat := 118140960795 + 1617573 * 2 ^ 59
def prefixEnd_1617573 : Nat := 4983230072969 + 3 ^ 40 * 1617573 * 2
def baseEnd_1617573 : Nat := 830592442735304971898423

theorem tailTrace_1617573 : CollatzResearch.WordTrace tailWord_1617573 prefixEnd_1617573 830592442735304971898423 := by
  unfold tailWord_1617573
  simp only [CollatzResearch.WordTrace]
  refine ⟨58997734168816755319369373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39331822779211170212912915 58997734168816755319369373)
  ·
    refine ⟨22124150313306283244763515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58997734168816755319369373 22124150313306283244763515)
    ·
      refine ⟨33186225469959424867145273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22124150313306283244763515 33186225469959424867145273)
      ·
        refine ⟨24889669102469568650358955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33186225469959424867145273 24889669102469568650358955)
        ·
          refine ⟨37334503653704352975538433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24889669102469568650358955 37334503653704352975538433)
          ·
            refine ⟨28000877740278264731653825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37334503653704352975538433 28000877740278264731653825)
            ·
              refine ⟨21000658305208698548740369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28000877740278264731653825 21000658305208698548740369)
              ·
                refine ⟨15750493728906523911555277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21000658305208698548740369 15750493728906523911555277)
                ·
                  refine ⟨5906435148339946466833229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15750493728906523911555277 5906435148339946466833229)
                  ·
                    refine ⟨2214913180627479925062461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5906435148339946466833229 2214913180627479925062461)
                    ·
                      refine ⟨830592442735304971898423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2214913180627479925062461 830592442735304971898423)
                      ·
                        rfl

theorem cell23_1617573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_1617573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617573 prefixEnd_1617573 := by exact prefixLift 1617573
  have htrace : WordTrace (prefixWord ++ tailWord_1617573) baseStart_1617573 baseEnd_1617573 := by
    simpa [prefixWord, tailWord_1617573, baseEnd_1617573] using wordTrace_append hprefix tailTrace_1617573
  have hstable : (prefixWord ++ tailWord_1617573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617573).length < 2 ^ (prefixWord ++ tailWord_1617573).sum := by decide
  have hdescent : baseEnd_1617573 < baseStart_1617573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617602 : List Nat := [3, 5, 1, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_1617602 : Nat := 118140960795 + 1617602 * 2 ^ 59
def prefixEnd_1617602 : Nat := 4983230072969 + 3 ^ 40 * 1617602 * 2
def baseEnd_1617602 : Nat := 830607333674285358435791

theorem tailTrace_1617602 : CollatzResearch.WordTrace tailWord_1617602 prefixEnd_1617602 830607333674285358435791 := by
  unfold tailWord_1617602
  simp only [CollatzResearch.WordTrace]
  refine ⟨14749697971427923318043765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39332527923807795514783373 14749697971427923318043765)
  ·
    refine ⟨1382784184821367811066603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14749697971427923318043765 1382784184821367811066603)
    ·
      refine ⟨2074176277232051716599905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1382784184821367811066603 2074176277232051716599905)
      ·
        refine ⟨1555632207924038787449929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2074176277232051716599905 1555632207924038787449929)
        ·
          refine ⟨1166724155943029090587447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1555632207924038787449929 1166724155943029090587447)
          ·
            refine ⟨1750086233914543635881171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166724155943029090587447 1750086233914543635881171)
            ·
              refine ⟨2625129350871815453821757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1750086233914543635881171 2625129350871815453821757)
              ·
                refine ⟨984423506576930795183159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2625129350871815453821757 984423506576930795183159)
                ·
                  refine ⟨1476635259865396192774739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 984423506576930795183159 1476635259865396192774739)
                  ·
                    refine ⟨2214952889798094289162109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1476635259865396192774739 2214952889798094289162109)
                    ·
                      refine ⟨830607333674285358435791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2214952889798094289162109 830607333674285358435791)
                      ·
                        rfl

theorem cell23_1617602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_1617602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617602 prefixEnd_1617602 := by exact prefixLift 1617602
  have htrace : WordTrace (prefixWord ++ tailWord_1617602) baseStart_1617602 baseEnd_1617602 := by
    simpa [prefixWord, tailWord_1617602, baseEnd_1617602] using wordTrace_append hprefix tailTrace_1617602
  have hstable : (prefixWord ++ tailWord_1617602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617602).length < 2 ^ (prefixWord ++ tailWord_1617602).sum := by decide
  have hdescent : baseEnd_1617602 < baseStart_1617602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617617 : List Nat := [1, 2, 2, 1, 2, 4, 2, 3, 1, 3, 2]
def baseStart_1617617 : Nat := 118140960795 + 1617617 * 2 ^ 59
def prefixEnd_1617617 : Nat := 4983230072969 + 3 ^ 40 * 1617617 * 2
def baseEnd_1617617 : Nat := 830615035884102799748221

theorem tailTrace_1617617 : CollatzResearch.WordTrace tailWord_1617617 prefixEnd_1617617 830615035884102799748221 := by
  unfold tailWord_1617617
  simp only [CollatzResearch.WordTrace]
  refine ⟨58999338980657350833971105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39332892653771567222647403 58999338980657350833971105)
  ·
    refine ⟨44249504235493013125478329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58999338980657350833971105 44249504235493013125478329)
    ·
      refine ⟨33187128176619759844108747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44249504235493013125478329 33187128176619759844108747)
      ·
        refine ⟨49780692264929639766163121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33187128176619759844108747 49780692264929639766163121)
        ·
          refine ⟨37335519198697229824622341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49780692264929639766163121 37335519198697229824622341)
          ·
            refine ⟨7000409849755730592116689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37335519198697229824622341 7000409849755730592116689)
            ·
              refine ⟨5250307387316797944087517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7000409849755730592116689 5250307387316797944087517)
              ·
                refine ⟨1968865270243799229032819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5250307387316797944087517 1968865270243799229032819)
                ·
                  refine ⟨2953297905365698843549229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1968865270243799229032819 2953297905365698843549229)
                  ·
                    refine ⟨1107486714512137066330961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2953297905365698843549229 1107486714512137066330961)
                    ·
                      refine ⟨830615035884102799748221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1107486714512137066330961 830615035884102799748221)
                      ·
                        rfl

theorem cell23_1617617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 3, 2].length) (baseStart_1617617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617617 prefixEnd_1617617 := by exact prefixLift 1617617
  have htrace : WordTrace (prefixWord ++ tailWord_1617617) baseStart_1617617 baseEnd_1617617 := by
    simpa [prefixWord, tailWord_1617617, baseEnd_1617617] using wordTrace_append hprefix tailTrace_1617617
  have hstable : (prefixWord ++ tailWord_1617617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617617).length < 2 ^ (prefixWord ++ tailWord_1617617).sum := by decide
  have hdescent : baseEnd_1617617 < baseStart_1617617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617643 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 4]
def baseStart_1617643 : Nat := 118140960795 + 1617643 * 2 ^ 59
def prefixEnd_1617643 : Nat := 4983230072969 + 3 ^ 40 * 1617643 * 2
def baseEnd_1617643 : Nat := 830628386381119698023101

theorem tailTrace_1617643 : CollatzResearch.WordTrace tailWord_1617643 prefixEnd_1617643 830628386381119698023101 := by
  unfold tailWord_1617643
  simp only [CollatzResearch.WordTrace]
  refine ⟨59000287278563157274417583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39333524852375438182945055 59000287278563157274417583)
  ·
    refine ⟨88500430917844735911626375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59000287278563157274417583 88500430917844735911626375)
    ·
      refine ⟨132750646376767103867439563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88500430917844735911626375 132750646376767103867439563)
      ·
        refine ⟨199125969565150655801159345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132750646376767103867439563 199125969565150655801159345)
        ·
          refine ⟨149344477173862991850869509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199125969565150655801159345 149344477173862991850869509)
          ·
            refine ⟨28002089470099310972038033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149344477173862991850869509 28002089470099310972038033)
            ·
              refine ⟨21001567102574483229028525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28002089470099310972038033 21001567102574483229028525)
              ·
                refine ⟨7875587663465431210885697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21001567102574483229028525 7875587663465431210885697)
                ·
                  refine ⟨5906690747599073408164273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7875587663465431210885697 5906690747599073408164273)
                  ·
                    refine ⟨4430018060699305056123205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5906690747599073408164273 4430018060699305056123205)
                    ·
                      refine ⟨830628386381119698023101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4430018060699305056123205 830628386381119698023101)
                      ·
                        rfl

theorem cell23_1617643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 4].length) (baseStart_1617643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617643 prefixEnd_1617643 := by exact prefixLift 1617643
  have htrace : WordTrace (prefixWord ++ tailWord_1617643) baseStart_1617643 baseEnd_1617643 := by
    simpa [prefixWord, tailWord_1617643, baseEnd_1617643] using wordTrace_append hprefix tailTrace_1617643
  have hstable : (prefixWord ++ tailWord_1617643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617643).length < 2 ^ (prefixWord ++ tailWord_1617643).sum := by decide
  have hdescent : baseEnd_1617643 < baseStart_1617643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617683 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 4, 5]
def baseStart_1617683 : Nat := 118140960795 + 1617683 * 2 ^ 59
def prefixEnd_1617683 : Nat := 4983230072969 + 3 ^ 40 * 1617683 * 2
def baseEnd_1617683 : Nat := 276882975202433180507639

theorem tailTrace_1617683 : CollatzResearch.WordTrace tailWord_1617683 prefixEnd_1617683 276882975202433180507639 := by
  unfold tailWord_1617683
  simp only [CollatzResearch.WordTrace]
  refine ⟨59001746198418244105873703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39334497465612162737249135 59001746198418244105873703)
  ·
    refine ⟨88502619297627366158810555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59001746198418244105873703 88502619297627366158810555)
    ·
      refine ⟨132753928946441049238215833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88502619297627366158810555 132753928946441049238215833)
      ·
        refine ⟨99565446709830786928661875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132753928946441049238215833 99565446709830786928661875)
        ·
          refine ⟨149348170064746180392992813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99565446709830786928661875 149348170064746180392992813)
          ·
            refine ⟨56005563774279817647372305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149348170064746180392992813 56005563774279817647372305)
            ·
              refine ⟨42004172830709863235529229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56005563774279817647372305 42004172830709863235529229)
              ·
                refine ⟨15751564811516198713323461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42004172830709863235529229 15751564811516198713323461)
                ·
                  refine ⟨2953418402159287258748149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15751564811516198713323461 2953418402159287258748149)
                  ·
                    refine ⟨276882975202433180507639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2953418402159287258748149 276882975202433180507639)
                    ·
                      rfl

theorem cell23_1617683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 5].length) (baseStart_1617683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617683 prefixEnd_1617683 := by exact prefixLift 1617683
  have htrace : WordTrace (prefixWord ++ tailWord_1617683) baseStart_1617683 baseEnd_1617683 := by
    simpa [prefixWord, tailWord_1617683, baseEnd_1617683] using wordTrace_append hprefix tailTrace_1617683
  have hstable : (prefixWord ++ tailWord_1617683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617683).length < 2 ^ (prefixWord ++ tailWord_1617683).sum := by decide
  have hdescent : baseEnd_1617683 < baseStart_1617683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617687 : List Nat := [1, 1, 3, 4, 2, 2, 1, 4, 5]
def baseStart_1617687 : Nat := 118140960795 + 1617687 * 2 ^ 59
def prefixEnd_1617687 : Nat := 4983230072969 + 3 ^ 40 * 1617687 * 2
def baseEnd_1617687 : Nat := 92294553281101947319211

theorem tailTrace_1617687 : CollatzResearch.WordTrace tailWord_1617687 prefixEnd_1617687 92294553281101947319211 := by
  unfold tailWord_1617687
  simp only [CollatzResearch.WordTrace]
  refine ⟨59001892090403752789019315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39334594726935835192679543 59001892090403752789019315)
  ·
    refine ⟨88502838135605629183528973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59001892090403752789019315 88502838135605629183528973)
    ·
      refine ⟨33188564300852110943823365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88502838135605629183528973 33188564300852110943823365)
      ·
        refine ⟨6222855806409770801966881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33188564300852110943823365 6222855806409770801966881)
        ·
          refine ⟨4667141854807328101475161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6222855806409770801966881 4667141854807328101475161)
          ·
            refine ⟨3500356391105496076106371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4667141854807328101475161 3500356391105496076106371)
            ·
              refine ⟨5250534586658244114159557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3500356391105496076106371 5250534586658244114159557)
              ·
                refine ⟨984475234998420771404917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5250534586658244114159557 984475234998420771404917)
                ·
                  refine ⟨92294553281101947319211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 984475234998420771404917 92294553281101947319211)
                  ·
                    rfl

theorem cell23_1617687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 5].length) (baseStart_1617687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617687 prefixEnd_1617687 := by exact prefixLift 1617687
  have htrace : WordTrace (prefixWord ++ tailWord_1617687) baseStart_1617687 baseEnd_1617687 := by
    simpa [prefixWord, tailWord_1617687, baseEnd_1617687] using wordTrace_append hprefix tailTrace_1617687
  have hstable : (prefixWord ++ tailWord_1617687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617687).length < 2 ^ (prefixWord ++ tailWord_1617687).sum := by decide
  have hdescent : baseEnd_1617687 < baseStart_1617687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617720 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 1, 3, 4]
def baseStart_1617720 : Nat := 118140960795 + 1617720 * 2 ^ 59
def prefixEnd_1617720 : Nat := 4983230072969 + 3 ^ 40 * 1617720 * 2
def baseEnd_1617720 : Nat := 830667924391515896760247

theorem tailTrace_1617720 : CollatzResearch.WordTrace tailWord_1617720 prefixEnd_1617720 830667924391515896760247 := by
  unfold tailWord_1617720
  simp only [CollatzResearch.WordTrace]
  refine ⟨29501547849642099712485307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39335397132856132949980409 29501547849642099712485307)
  ·
    refine ⟨44252321774463149568727961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29501547849642099712485307 44252321774463149568727961)
    ·
      refine ⟨33189241330847362176545971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44252321774463149568727961 33189241330847362176545971)
      ·
        refine ⟨49783861996271043264818957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33189241330847362176545971 49783861996271043264818957)
        ·
          refine ⟨18668948248601641224307109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49783861996271043264818957 18668948248601641224307109)
          ·
            refine ⟨3500427796612807729557583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18668948248601641224307109 3500427796612807729557583)
            ·
              refine ⟨5250641694919211594336375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3500427796612807729557583 5250641694919211594336375)
              ·
                refine ⟨7875962542378817391504563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5250641694919211594336375 7875962542378817391504563)
                ·
                  refine ⟨11813943813568226087256845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7875962542378817391504563 11813943813568226087256845)
                  ·
                    refine ⟨4430228930088084782721317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11813943813568226087256845 4430228930088084782721317)
                    ·
                      refine ⟨830667924391515896760247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4430228930088084782721317 830667924391515896760247)
                      ·
                        rfl

theorem cell23_1617720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_1617720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617720 prefixEnd_1617720 := by exact prefixLift 1617720
  have htrace : WordTrace (prefixWord ++ tailWord_1617720) baseStart_1617720 baseEnd_1617720 := by
    simpa [prefixWord, tailWord_1617720, baseEnd_1617720] using wordTrace_append hprefix tailTrace_1617720
  have hstable : (prefixWord ++ tailWord_1617720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617720).length < 2 ^ (prefixWord ++ tailWord_1617720).sum := by decide
  have hdescent : baseEnd_1617720 < baseStart_1617720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617733 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 1, 3, 6]
def baseStart_1617733 : Nat := 118140960795 + 1617733 * 2 ^ 59
def prefixEnd_1617733 : Nat := 4983230072969 + 3 ^ 40 * 1617733 * 2
def baseEnd_1617733 : Nat := 830674599640024345897687

theorem tailTrace_1617733 : CollatzResearch.WordTrace tailWord_1617733 prefixEnd_1617733 830674599640024345897687 := by
  unfold tailWord_1617733
  simp only [CollatzResearch.WordTrace]
  refine ⟨59003569848237102645193853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39335713232158068430129235 59003569848237102645193853)
  ·
    refine ⟨22126338693088913491947695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59003569848237102645193853 22126338693088913491947695)
    ·
      refine ⟨33189508039633370237921543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22126338693088913491947695 33189508039633370237921543)
      ·
        refine ⟨49784262059450055356882315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33189508039633370237921543 49784262059450055356882315)
        ·
          refine ⟨74676393089175083035323473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49784262059450055356882315 74676393089175083035323473)
          ·
            refine ⟨56007294816881312276492605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74676393089175083035323473 56007294816881312276492605)
            ·
              refine ⟨21002735556330492103684727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56007294816881312276492605 21002735556330492103684727)
              ·
                refine ⟨31504103334495738155527091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21002735556330492103684727 31504103334495738155527091)
                ·
                  refine ⟨47256155001743607233290637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31504103334495738155527091 47256155001743607233290637)
                  ·
                    refine ⟨17721058125653852712483989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47256155001743607233290637 17721058125653852712483989)
                    ·
                      refine ⟨830674599640024345897687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17721058125653852712483989 830674599640024345897687)
                      ·
                        rfl

theorem cell23_1617733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_1617733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617733 prefixEnd_1617733 := by exact prefixLift 1617733
  have htrace : WordTrace (prefixWord ++ tailWord_1617733) baseStart_1617733 baseEnd_1617733 := by
    simpa [prefixWord, tailWord_1617733, baseEnd_1617733] using wordTrace_append hprefix tailTrace_1617733
  have hstable : (prefixWord ++ tailWord_1617733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617733).length < 2 ^ (prefixWord ++ tailWord_1617733).sum := by decide
  have hdescent : baseEnd_1617733 < baseStart_1617733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617831 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_1617831 : Nat := 118140960795 + 1617831 * 2 ^ 59
def prefixEnd_1617831 : Nat := 4983230072969 + 3 ^ 40 * 1617831 * 2
def baseEnd_1617831 : Nat := 830724920744164962472237

theorem tailTrace_1617831 : CollatzResearch.WordTrace tailWord_1617831 prefixEnd_1617831 830724920744164962472237 := by
  unfold tailWord_1617831
  simp only [CollatzResearch.WordTrace]
  refine ⟨59007144201882065382261347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39338096134588043588174231 59007144201882065382261347)
  ·
    refine ⟨88510716302823098073392021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59007144201882065382261347 88510716302823098073392021)
    ·
      refine ⟨4148939826694832722190251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88510716302823098073392021 4148939826694832722190251)
      ·
        refine ⟨6223409740042249083285377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4148939826694832722190251 6223409740042249083285377)
        ·
          refine ⟨4667557305031686812464033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6223409740042249083285377 4667557305031686812464033)
          ·
            refine ⟨3500667978773765109348025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4667557305031686812464033 3500667978773765109348025)
            ·
              refine ⟨2625500984080323832011019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3500667978773765109348025 2625500984080323832011019)
              ·
                refine ⟨3938251476120485748016529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2625500984080323832011019 3938251476120485748016529)
                ·
                  refine ⟨2953688607090364311012397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3938251476120485748016529 2953688607090364311012397)
                  ·
                    refine ⟨1107633227658886616629649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2953688607090364311012397 1107633227658886616629649)
                    ·
                      refine ⟨830724920744164962472237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1107633227658886616629649 830724920744164962472237)
                      ·
                        rfl

theorem cell23_1617831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_1617831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617831 prefixEnd_1617831 := by exact prefixLift 1617831
  have htrace : WordTrace (prefixWord ++ tailWord_1617831) baseStart_1617831 baseEnd_1617831 := by
    simpa [prefixWord, tailWord_1617831, baseEnd_1617831] using wordTrace_append hprefix tailTrace_1617831
  have hstable : (prefixWord ++ tailWord_1617831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617831).length < 2 ^ (prefixWord ++ tailWord_1617831).sum := by decide
  have hdescent : baseEnd_1617831 < baseStart_1617831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617854 : List Nat := [4, 2, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_1617854 : Nat := 118140960795 + 1617854 * 2 ^ 59
def prefixEnd_1617854 : Nat := 4983230072969 + 3 ^ 40 * 1617854 * 2
def baseEnd_1617854 : Nat := 276912243599739457494877

theorem tailTrace_1617854 : CollatzResearch.WordTrace tailWord_1617854 prefixEnd_1617854 276912243599739457494877 := by
  unfold tailWord_1617854
  simp only [CollatzResearch.WordTrace]
  refine ⟨7375997885099842538793577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39338655387199160206899077 7375997885099842538793577)
  ·
    refine ⟨5531998413824881904095183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7375997885099842538793577 5531998413824881904095183)
    ·
      refine ⟨8297997620737322856142775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5531998413824881904095183 8297997620737322856142775)
      ·
        refine ⟨12446996431105984284214163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8297997620737322856142775 12446996431105984284214163)
        ·
          refine ⟨18670494646658976426321245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12446996431105984284214163 18670494646658976426321245)
          ·
            refine ⟨7001435492497116159870467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18670494646658976426321245 7001435492497116159870467)
            ·
              refine ⟨10502153238745674239805701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7001435492497116159870467 10502153238745674239805701)
              ·
                refine ⟨1969153732264813919963569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10502153238745674239805701 1969153732264813919963569)
                ·
                  refine ⟨1476865299198610439972677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1969153732264813919963569 1476865299198610439972677)
                  ·
                    refine ⟨276912243599739457494877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1476865299198610439972677 276912243599739457494877)
                    ·
                      rfl

theorem cell23_1617854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_1617854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617854 prefixEnd_1617854 := by exact prefixLift 1617854
  have htrace : WordTrace (prefixWord ++ tailWord_1617854) baseStart_1617854 baseEnd_1617854 := by
    simpa [prefixWord, tailWord_1617854, baseEnd_1617854] using wordTrace_append hprefix tailTrace_1617854
  have hstable : (prefixWord ++ tailWord_1617854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617854).length < 2 ^ (prefixWord ++ tailWord_1617854).sum := by decide
  have hdescent : baseEnd_1617854 < baseStart_1617854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617880 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 2, 7]
def baseStart_1617880 : Nat := 118140960795 + 1617880 * 2 ^ 59
def prefixEnd_1617880 : Nat := 4983230072969 + 3 ^ 40 * 1617880 * 2
def baseEnd_1617880 : Nat := 276916693765411756919837

theorem tailTrace_1617880 : CollatzResearch.WordTrace tailWord_1617880 prefixEnd_1617880 276916693765411756919837 := by
  unfold tailWord_1617880
  simp only [CollatzResearch.WordTrace]
  refine ⟨29504465689352273375397547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39339287585803031167196729 29504465689352273375397547)
  ·
    refine ⟨44256698534028410063096321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29504465689352273375397547 44256698534028410063096321)
    ·
      refine ⟨33192523900521307547322241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44256698534028410063096321 33192523900521307547322241)
      ·
        refine ⟨24894392925390980660491681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33192523900521307547322241 24894392925390980660491681)
        ·
          refine ⟨18670794694043235495368761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24894392925390980660491681 18670794694043235495368761)
          ·
            refine ⟨14003096020532426621526571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18670794694043235495368761 14003096020532426621526571)
            ·
              refine ⟨21004644030798639932289857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14003096020532426621526571 21004644030798639932289857)
              ·
                refine ⟨15753483023098979949217393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21004644030798639932289857 15753483023098979949217393)
                ·
                  refine ⟨11815112267324234961913045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15753483023098979949217393 11815112267324234961913045)
                  ·
                    refine ⟨276916693765411756919837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11815112267324234961913045 276916693765411756919837)
                    ·
                      rfl

theorem cell23_1617880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_1617880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617880 prefixEnd_1617880 := by exact prefixLift 1617880
  have htrace : WordTrace (prefixWord ++ tailWord_1617880) baseStart_1617880 baseEnd_1617880 := by
    simpa [prefixWord, tailWord_1617880, baseEnd_1617880] using wordTrace_append hprefix tailTrace_1617880
  have hstable : (prefixWord ++ tailWord_1617880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617880).length < 2 ^ (prefixWord ++ tailWord_1617880).sum := by decide
  have hdescent : baseEnd_1617880 < baseStart_1617880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617895 : List Nat := [1, 1, 5, 2, 3, 1, 2, 3, 1, 2, 2]
def baseStart_1617895 : Nat := 118140960795 + 1617895 * 2 ^ 59
def prefixEnd_1617895 : Nat := 4983230072969 + 3 ^ 40 * 1617895 * 2
def baseEnd_1617895 : Nat := 830757783506052712071943

theorem tailTrace_1617895 : CollatzResearch.WordTrace tailWord_1617895 prefixEnd_1617895 830757783506052712071943 := by
  unfold tailWord_1617895
  simp only [CollatzResearch.WordTrace]
  refine ⟨59009478473650204312591139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39339652315766802875060759 59009478473650204312591139)
  ·
    refine ⟨88514217710475306468886709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59009478473650204312591139 88514217710475306468886709)
    ·
      refine ⟨8298207910357059981458129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88514217710475306468886709 8298207910357059981458129)
      ·
        refine ⟨6223655932767794986093597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8298207910357059981458129 6223655932767794986093597)
        ·
          refine ⟨2333870974787923119785099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6223655932767794986093597 2333870974787923119785099)
          ·
            refine ⟨3500806462181884679677649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2333870974787923119785099 3500806462181884679677649)
            ·
              refine ⟨2625604846636413509758237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3500806462181884679677649 2625604846636413509758237)
              ·
                refine ⟨984601817488655066159339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2625604846636413509758237 984601817488655066159339)
                ·
                  refine ⟨1476902726232982599239009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 984601817488655066159339 1476902726232982599239009)
                  ·
                    refine ⟨1107677044674736949429257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1476902726232982599239009 1107677044674736949429257)
                    ·
                      refine ⟨830757783506052712071943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1107677044674736949429257 830757783506052712071943)
                      ·
                        rfl

theorem cell23_1617895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_1617895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617895 prefixEnd_1617895 := by exact prefixLift 1617895
  have htrace : WordTrace (prefixWord ++ tailWord_1617895) baseStart_1617895 baseEnd_1617895 := by
    simpa [prefixWord, tailWord_1617895, baseEnd_1617895] using wordTrace_append hprefix tailTrace_1617895
  have hstable : (prefixWord ++ tailWord_1617895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617895).length < 2 ^ (prefixWord ++ tailWord_1617895).sum := by decide
  have hdescent : baseEnd_1617895 < baseStart_1617895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617920 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 5]
def baseStart_1617920 : Nat := 118140960795 + 1617920 * 2 ^ 59
def prefixEnd_1617920 : Nat := 4983230072969 + 3 ^ 40 * 1617920 * 2
def baseEnd_1617920 : Nat := 830770620522415114259327

theorem tailTrace_1617920 : CollatzResearch.WordTrace tailWord_1617920 prefixEnd_1617920 830770620522415114259327 := by
  unfold tailWord_1617920
  simp only [CollatzResearch.WordTrace]
  refine ⟨29505195149279816791125607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39340260199039755721500809 29505195149279816791125607)
  ·
    refine ⟨44257792723919725186688411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29505195149279816791125607 44257792723919725186688411)
    ·
      refine ⟨66386689085879587780032617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44257792723919725186688411 66386689085879587780032617)
      ·
        refine ⟨49790016814409690835024463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66386689085879587780032617 49790016814409690835024463)
        ·
          refine ⟨74685025221614536252536695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49790016814409690835024463 74685025221614536252536695)
          ·
            refine ⟨112027537832421804378805043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74685025221614536252536695 112027537832421804378805043)
            ·
              refine ⟨168041306748632706568207565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112027537832421804378805043 168041306748632706568207565)
              ·
                refine ⟨63015490030737264963077837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168041306748632706568207565 63015490030737264963077837)
                ·
                  refine ⟨23630808761526474361154189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63015490030737264963077837 23630808761526474361154189)
                  ·
                    refine ⟨8861553285572427885432821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23630808761526474361154189 8861553285572427885432821)
                    ·
                      refine ⟨830770620522415114259327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8861553285572427885432821 830770620522415114259327)
                      ·
                        rfl

theorem cell23_1617920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_1617920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617920 prefixEnd_1617920 := by exact prefixLift 1617920
  have htrace : WordTrace (prefixWord ++ tailWord_1617920) baseStart_1617920 baseEnd_1617920 := by
    simpa [prefixWord, tailWord_1617920, baseEnd_1617920] using wordTrace_append hprefix tailTrace_1617920
  have hstable : (prefixWord ++ tailWord_1617920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617920).length < 2 ^ (prefixWord ++ tailWord_1617920).sum := by decide
  have hdescent : baseEnd_1617920 < baseStart_1617920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617927 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 2, 6]
def baseStart_1617927 : Nat := 118140960795 + 1617927 * 2 ^ 59
def prefixEnd_1617927 : Nat := 4983230072969 + 3 ^ 40 * 1617927 * 2
def baseEnd_1617927 : Nat := 276924738295665528957265

theorem tailTrace_1617927 : CollatzResearch.WordTrace tailWord_1617927 prefixEnd_1617927 276924738295665528957265 := by
  unfold tailWord_1617927
  simp only [CollatzResearch.WordTrace]
  refine ⟨59010645609534273777756035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39340430406356182518504023 59010645609534273777756035)
  ·
    refine ⟨88515968414301410666634053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59010645609534273777756035 88515968414301410666634053)
    ·
      refine ⟨16596744077681514499993885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88515968414301410666634053 16596744077681514499993885)
      ·
        refine ⟨6223779029130567937497707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16596744077681514499993885 6223779029130567937497707)
        ·
          refine ⟨9335668543695851906246561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6223779029130567937497707 9335668543695851906246561)
          ·
            refine ⟨7001751407771888929684921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9335668543695851906246561 7001751407771888929684921)
            ·
              refine ⟨5251313555828916697263691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7001751407771888929684921 5251313555828916697263691)
              ·
                refine ⟨7876970333743375045895537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5251313555828916697263691 7876970333743375045895537)
                ·
                  refine ⟨5907727750307531284421653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7876970333743375045895537 5907727750307531284421653)
                  ·
                    refine ⟨276924738295665528957265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5907727750307531284421653 276924738295665528957265)
                    ·
                      rfl

theorem cell23_1617927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_1617927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617927 prefixEnd_1617927 := by exact prefixLift 1617927
  have htrace : WordTrace (prefixWord ++ tailWord_1617927) baseStart_1617927 baseEnd_1617927 := by
    simpa [prefixWord, tailWord_1617927, baseEnd_1617927] using wordTrace_append hprefix tailTrace_1617927
  have hstable : (prefixWord ++ tailWord_1617927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617927).length < 2 ^ (prefixWord ++ tailWord_1617927).sum := by decide
  have hdescent : baseEnd_1617927 < baseStart_1617927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617967 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 3]
def baseStart_1617967 : Nat := 118140960795 + 1617967 * 2 ^ 59
def prefixEnd_1617967 : Nat := 4983230072969 + 3 ^ 40 * 1617967 * 2
def baseEnd_1617967 : Nat := 830794754113176430371611

theorem tailTrace_1617967 : CollatzResearch.WordTrace tailWord_1617967 prefixEnd_1617967 830794754113176430371611 := by
  unfold tailWord_1617967
  simp only [CollatzResearch.WordTrace]
  refine ⟨59012104529389360609212155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39341403019592907072808103 59012104529389360609212155)
  ·
    refine ⟨88518156794084040913818233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59012104529389360609212155 88518156794084040913818233)
    ·
      refine ⟨66388617595563030685363675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88518156794084040913818233 66388617595563030685363675)
      ·
        refine ⟨99582926393344546028045513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66388617595563030685363675 99582926393344546028045513)
        ·
          refine ⟨74687194795008409521034135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99582926393344546028045513 74687194795008409521034135)
          ·
            refine ⟨112030792192512614281551203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74687194795008409521034135 112030792192512614281551203)
            ·
              refine ⟨168046188288768921422326805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112030792192512614281551203 168046188288768921422326805)
              ·
                refine ⟨7877165076036043191671569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 168046188288768921422326805 7877165076036043191671569)
                ·
                  refine ⟨5907873807027032393753677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7877165076036043191671569 5907873807027032393753677)
                  ·
                    refine ⟨2215452677635137147657629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5907873807027032393753677 2215452677635137147657629)
                    ·
                      refine ⟨830794754113176430371611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2215452677635137147657629 830794754113176430371611)
                      ·
                        rfl

theorem cell23_1617967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 3].length) (baseStart_1617967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617967 prefixEnd_1617967 := by exact prefixLift 1617967
  have htrace : WordTrace (prefixWord ++ tailWord_1617967) baseStart_1617967 baseEnd_1617967 := by
    simpa [prefixWord, tailWord_1617967, baseEnd_1617967] using wordTrace_append hprefix tailTrace_1617967
  have hstable : (prefixWord ++ tailWord_1617967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617967).length < 2 ^ (prefixWord ++ tailWord_1617967).sum := by decide
  have hdescent : baseEnd_1617967 < baseStart_1617967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617985 : List Nat := [1, 2, 5, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_1617985 : Nat := 118140960795 + 1617985 * 2 ^ 59
def prefixEnd_1617985 : Nat := 4983230072969 + 3 ^ 40 * 1617985 * 2
def baseEnd_1617985 : Nat := 830803996764957359946529

theorem tailTrace_1617985 : CollatzResearch.WordTrace tailWord_1617985 prefixEnd_1617985 830803996764957359946529 := by
  unfold tailWord_1617985
  simp only [CollatzResearch.WordTrace]
  refine ⟨59012761043324149683367409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39341840695549433122244939 59012761043324149683367409)
  ·
    refine ⟨44259570782493112262525557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59012761043324149683367409 44259570782493112262525557)
    ·
      refine ⟨4149334760858729274611771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44259570782493112262525557 4149334760858729274611771)
      ·
        refine ⟨6224002141288093911917657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4149334760858729274611771 6224002141288093911917657)
        ·
          refine ⟨4668001605966070433938243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6224002141288093911917657 4668001605966070433938243)
          ·
            refine ⟨7002002408949105650907365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4668001605966070433938243 7002002408949105650907365)
            ·
              refine ⟨1312875451677957309545131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7002002408949105650907365 1312875451677957309545131)
              ·
                refine ⟨1969313177516935964317697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1312875451677957309545131 1969313177516935964317697)
                ·
                  refine ⟨1476984883137701973238273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1969313177516935964317697 1476984883137701973238273)
                  ·
                    refine ⟨1107738662353276479928705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1476984883137701973238273 1107738662353276479928705)
                    ·
                      refine ⟨830803996764957359946529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1107738662353276479928705 830803996764957359946529)
                      ·
                        rfl

theorem cell23_1617985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_1617985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1617985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1617985 prefixEnd_1617985 := by exact prefixLift 1617985
  have htrace : WordTrace (prefixWord ++ tailWord_1617985) baseStart_1617985 baseEnd_1617985 := by
    simpa [prefixWord, tailWord_1617985, baseEnd_1617985] using wordTrace_append hprefix tailTrace_1617985
  have hstable : (prefixWord ++ tailWord_1617985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617985).length < 2 ^ (prefixWord ++ tailWord_1617985).sum := by decide
  have hdescent : baseEnd_1617985 < baseStart_1617985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618007 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 4]
def baseStart_1618007 : Nat := 118140960795 + 1618007 * 2 ^ 59
def prefixEnd_1618007 : Nat := 4983230072969 + 3 ^ 40 * 1618007 * 2
def baseEnd_1618007 : Nat := 830815293339356273871427

theorem tailTrace_1618007 : CollatzResearch.WordTrace tailWord_1618007 prefixEnd_1618007 830815293339356273871427 := by
  unfold tailWord_1618007
  simp only [CollatzResearch.WordTrace]
  refine ⟨59013563449244447440668275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39342375632829631627112183 59013563449244447440668275)
  ·
    refine ⟨88520345173866671161002413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59013563449244447440668275 88520345173866671161002413)
    ·
      refine ⟨33195129440200001685375905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88520345173866671161002413 33195129440200001685375905)
      ·
        refine ⟨24896347080150001264031929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33195129440200001685375905 24896347080150001264031929)
        ·
          refine ⟨18672260310112500948023947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24896347080150001264031929 18672260310112500948023947)
          ·
            refine ⟨28008390465168751422035921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18672260310112500948023947 28008390465168751422035921)
            ·
              refine ⟨21006292848876563566526941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28008390465168751422035921 21006292848876563566526941)
              ·
                refine ⟨7877359818328711337447603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21006292848876563566526941 7877359818328711337447603)
                ·
                  refine ⟨11816039727493067006171405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7877359818328711337447603 11816039727493067006171405)
                  ·
                    refine ⟨4431014897809900127314277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11816039727493067006171405 4431014897809900127314277)
                    ·
                      refine ⟨830815293339356273871427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4431014897809900127314277 830815293339356273871427)
                      ·
                        rfl

theorem cell23_1618007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_1618007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618007 prefixEnd_1618007 := by exact prefixLift 1618007
  have htrace : WordTrace (prefixWord ++ tailWord_1618007) baseStart_1618007 baseEnd_1618007 := by
    simpa [prefixWord, tailWord_1618007, baseEnd_1618007] using wordTrace_append hprefix tailTrace_1618007
  have hstable : (prefixWord ++ tailWord_1618007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618007).length < 2 ^ (prefixWord ++ tailWord_1618007).sum := by decide
  have hdescent : baseEnd_1618007 < baseStart_1618007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618041 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 2, 4, 2]
def baseStart_1618041 : Nat := 118140960795 + 1618041 * 2 ^ 59
def prefixEnd_1618041 : Nat := 4983230072969 + 3 ^ 40 * 1618041 * 2
def baseEnd_1618041 : Nat := 830832751681609140846271

theorem tailTrace_1618041 : CollatzResearch.WordTrace tailWord_1618041 prefixEnd_1618041 830832751681609140846271 := by
  unfold tailWord_1618041
  simp only [CollatzResearch.WordTrace]
  refine ⟨59014803531121271247405977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39343202354080847498270651 59014803531121271247405977)
  ·
    refine ⟨44261102648340953435554483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59014803531121271247405977 44261102648340953435554483)
    ·
      refine ⟨66391653972511430153331725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44261102648340953435554483 66391653972511430153331725)
      ·
        refine ⟨24896870239691786307499397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66391653972511430153331725 24896870239691786307499397)
        ·
          refine ⟨4668163169942209932656137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24896870239691786307499397 4668163169942209932656137)
          ·
            refine ⟨3501122377456657449492103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4668163169942209932656137 3501122377456657449492103)
            ·
              refine ⟨5251683566184986174238155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3501122377456657449492103 5251683566184986174238155)
              ·
                refine ⟨7877525349277479261357233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5251683566184986174238155 7877525349277479261357233)
                ·
                  refine ⟨5908144011958109446017925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7877525349277479261357233 5908144011958109446017925)
                  ·
                    refine ⟨1107777002242145521128361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5908144011958109446017925 1107777002242145521128361)
                    ·
                      refine ⟨830832751681609140846271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1107777002242145521128361 830832751681609140846271)
                      ·
                        rfl

theorem cell23_1618041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_1618041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618041 prefixEnd_1618041 := by exact prefixLift 1618041
  have htrace : WordTrace (prefixWord ++ tailWord_1618041) baseStart_1618041 baseEnd_1618041 := by
    simpa [prefixWord, tailWord_1618041, baseEnd_1618041] using wordTrace_append hprefix tailTrace_1618041
  have hstable : (prefixWord ++ tailWord_1618041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618041).length < 2 ^ (prefixWord ++ tailWord_1618041).sum := by decide
  have hdescent : baseEnd_1618041 < baseStart_1618041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618081 : List Nat := [1, 2, 3, 3, 1, 4, 1, 2, 6]
def baseStart_1618081 : Nat := 118140960795 + 1618081 * 2 ^ 59
def prefixEnd_1618081 : Nat := 4983230072969 + 3 ^ 40 * 1618081 * 2
def baseEnd_1618081 : Nat := 92317032323087664927343

theorem tailTrace_1618081 : CollatzResearch.WordTrace tailWord_1618081 prefixEnd_1618081 92317032323087664927343 := by
  unfold tailWord_1618081
  simp only [CollatzResearch.WordTrace]
  refine ⟨59016262450976358078862097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39344174967317572052574731 59016262450976358078862097)
  ·
    refine ⟨44262196838232268559146573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59016262450976358078862097 44262196838232268559146573)
    ·
      refine ⟨16598323814337100709679965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44262196838232268559146573 16598323814337100709679965)
      ·
        refine ⟨6224371430376412766129987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16598323814337100709679965 6224371430376412766129987)
        ·
          refine ⟨9336557145564619149194981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6224371430376412766129987 9336557145564619149194981)
          ·
            refine ⟨1750604464793366090474059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9336557145564619149194981 1750604464793366090474059)
            ·
              refine ⟨2625906697190049135711089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1750604464793366090474059 2625906697190049135711089)
              ·
                refine ⟨1969430022892536851783317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2625906697190049135711089 1969430022892536851783317)
                ·
                  refine ⟨92317032323087664927343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1969430022892536851783317 92317032323087664927343)
                  ·
                    rfl

theorem cell23_1618081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 6].length) (baseStart_1618081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618081 prefixEnd_1618081 := by exact prefixLift 1618081
  have htrace : WordTrace (prefixWord ++ tailWord_1618081) baseStart_1618081 baseEnd_1618081 := by
    simpa [prefixWord, tailWord_1618081, baseEnd_1618081] using wordTrace_append hprefix tailTrace_1618081
  have hstable : (prefixWord ++ tailWord_1618081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618081).length < 2 ^ (prefixWord ++ tailWord_1618081).sum := by decide
  have hdescent : baseEnd_1618081 < baseStart_1618081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618137 : List Nat := [1, 2, 1, 2, 3, 1, 13]
def baseStart_1618137 : Nat := 118140960795 + 1618137 * 2 ^ 59
def prefixEnd_1618137 : Nat := 4983230072969 + 3 ^ 40 * 1618137 * 2
def baseEnd_1618137 : Nat := 10257803034869639077109

theorem tailTrace_1618137 : CollatzResearch.WordTrace tailWord_1618137 prefixEnd_1618137 10257803034869639077109 := by
  unfold tailWord_1618137
  simp only [CollatzResearch.WordTrace]
  refine ⟨59018304938773479642900665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39345536625848986428600443 59018304938773479642900665)
  ·
    refine ⟨44263728704080109732175499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59018304938773479642900665 44263728704080109732175499)
    ·
      refine ⟨66395593056120164598263249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44263728704080109732175499 66395593056120164598263249)
      ·
        refine ⟨49796694792090123448697437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66395593056120164598263249 49796694792090123448697437)
        ·
          refine ⟨18673760547033796293261539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49796694792090123448697437 18673760547033796293261539)
          ·
            refine ⟨28010640820550694439892309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18673760547033796293261539 28010640820550694439892309)
            ·
              refine ⟨10257803034869639077109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 28010640820550694439892309 10257803034869639077109)
              ·
                rfl

theorem cell23_1618137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 13].length) (baseStart_1618137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618137 prefixEnd_1618137 := by exact prefixLift 1618137
  have htrace : WordTrace (prefixWord ++ tailWord_1618137) baseStart_1618137 baseEnd_1618137 := by
    simpa [prefixWord, tailWord_1618137, baseEnd_1618137] using wordTrace_append hprefix tailTrace_1618137
  have hstable : (prefixWord ++ tailWord_1618137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618137).length < 2 ^ (prefixWord ++ tailWord_1618137).sum := by decide
  have hdescent : baseEnd_1618137 < baseStart_1618137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618151 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1618151 : Nat := 118140960795 + 1618151 * 2 ^ 59
def prefixEnd_1618151 : Nat := 4983230072969 + 3 ^ 40 * 1618151 * 2
def baseEnd_1618151 : Nat := 830889234553603710470765

theorem tailTrace_1618151 : CollatzResearch.WordTrace tailWord_1618151 prefixEnd_1618151 830889234553603710470765 := by
  unfold tailWord_1618151
  simp only [CollatzResearch.WordTrace]
  refine ⟨59018815560722760033910307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39345877040481840022606871 59018815560722760033910307)
  ·
    refine ⟨88528223341084140050865461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59018815560722760033910307 88528223341084140050865461)
    ·
      refine ⟨8299520938226638129768637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88528223341084140050865461 8299520938226638129768637)
      ·
        refine ⟨3112320351834989298663239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8299520938226638129768637 3112320351834989298663239)
        ·
          refine ⟨4668480527752483947994859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3112320351834989298663239 4668480527752483947994859)
          ·
            refine ⟨7002720791628725921992289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4668480527752483947994859 7002720791628725921992289)
            ·
              refine ⟨5252040593721544441494217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7002720791628725921992289 5252040593721544441494217)
              ·
                refine ⟨3939030445291158331120663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5252040593721544441494217 3939030445291158331120663)
                ·
                  refine ⟨5908545667936737496680995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3939030445291158331120663 5908545667936737496680995)
                  ·
                    refine ⟨8862818501905106245021493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5908545667936737496680995 8862818501905106245021493)
                    ·
                      refine ⟨830889234553603710470765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8862818501905106245021493 830889234553603710470765)
                      ·
                        rfl

theorem cell23_1618151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1618151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618151 prefixEnd_1618151 := by exact prefixLift 1618151
  have htrace : WordTrace (prefixWord ++ tailWord_1618151) baseStart_1618151 baseEnd_1618151 := by
    simpa [prefixWord, tailWord_1618151, baseEnd_1618151] using wordTrace_append hprefix tailTrace_1618151
  have hstable : (prefixWord ++ tailWord_1618151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618151).length < 2 ^ (prefixWord ++ tailWord_1618151).sum := by decide
  have hdescent : baseEnd_1618151 < baseStart_1618151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618154 : List Nat := [3, 1, 3, 1, 1, 2, 4, 8]
def baseStart_1618154 : Nat := 118140960795 + 1618154 * 2 ^ 59
def prefixEnd_1618154 : Nat := 4983230072969 + 3 ^ 40 * 1618154 * 2
def baseEnd_1618154 : Nat := 30773732407243229582713

theorem tailTrace_1618154 : CollatzResearch.WordTrace tailWord_1618154 prefixEnd_1618154 30773732407243229582713 := by
  unfold tailWord_1618154
  simp only [CollatzResearch.WordTrace]
  refine ⟨14754731244927972886567379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39345949986474594364179677 14754731244927972886567379)
  ·
    refine ⟨22132096867391959329851069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14754731244927972886567379 22132096867391959329851069)
    ·
      refine ⟨8299536325271984748694151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22132096867391959329851069 8299536325271984748694151)
      ·
        refine ⟨12449304487907977123041227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8299536325271984748694151 12449304487907977123041227)
        ·
          refine ⟨18673956731861965684561841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12449304487907977123041227 18673956731861965684561841)
          ·
            refine ⟨14005467548896474263421381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18673956731861965684561841 14005467548896474263421381)
            ·
              refine ⟨2626025165418088924391509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14005467548896474263421381 2626025165418088924391509)
              ·
                refine ⟨30773732407243229582713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2626025165418088924391509 30773732407243229582713)
                ·
                  rfl

theorem cell23_1618154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 8].length) (baseStart_1618154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618154 prefixEnd_1618154 := by exact prefixLift 1618154
  have htrace : WordTrace (prefixWord ++ tailWord_1618154) baseStart_1618154 baseEnd_1618154 := by
    simpa [prefixWord, tailWord_1618154, baseEnd_1618154] using wordTrace_append hprefix tailTrace_1618154
  have hstable : (prefixWord ++ tailWord_1618154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618154).length < 2 ^ (prefixWord ++ tailWord_1618154).sum := by decide
  have hdescent : baseEnd_1618154 < baseStart_1618154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618178 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_1618178 : Nat := 118140960795 + 1618178 * 2 ^ 59
def prefixEnd_1618178 : Nat := 4983230072969 + 3 ^ 40 * 1618178 * 2
def baseEnd_1618178 : Nat := 830903098531275104833141

theorem tailTrace_1618178 : CollatzResearch.WordTrace tailWord_1618178 prefixEnd_1618178 830903098531275104833141 := by
  unfold tailWord_1618178
  simp only [CollatzResearch.WordTrace]
  refine ⟨14754950082906235911285797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39346533554416629096762125 14754950082906235911285797)
  ·
    refine ⟨2766553140544919233366087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14754950082906235911285797 2766553140544919233366087)
    ·
      refine ⟨4149829710817378850049131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2766553140544919233366087 4149829710817378850049131)
      ·
        refine ⟨6224744566226068275073697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4149829710817378850049131 6224744566226068275073697)
        ·
          refine ⟨4668558424669551206305273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6224744566226068275073697 4668558424669551206305273)
          ·
            refine ⟨3501418818502163404728955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4668558424669551206305273 3501418818502163404728955)
            ·
              refine ⟨5252128227753245107093433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3501418818502163404728955 5252128227753245107093433)
              ·
                refine ⟨3939096170814933830320075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5252128227753245107093433 3939096170814933830320075)
                ·
                  refine ⟨5908644256222400745480113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3939096170814933830320075 5908644256222400745480113)
                  ·
                    refine ⟨4431483192166800559110085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5908644256222400745480113 4431483192166800559110085)
                    ·
                      refine ⟨830903098531275104833141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4431483192166800559110085 830903098531275104833141)
                      ·
                        rfl

theorem cell23_1618178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_1618178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618178 prefixEnd_1618178 := by exact prefixLift 1618178
  have htrace : WordTrace (prefixWord ++ tailWord_1618178) baseStart_1618178 baseEnd_1618178 := by
    simpa [prefixWord, tailWord_1618178, baseEnd_1618178] using wordTrace_append hprefix tailTrace_1618178
  have hstable : (prefixWord ++ tailWord_1618178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618178).length < 2 ^ (prefixWord ++ tailWord_1618178).sum := by decide
  have hdescent : baseEnd_1618178 < baseStart_1618178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618181 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 4, 1, 3]
def baseStart_1618181 : Nat := 118140960795 + 1618181 * 2 ^ 59
def prefixEnd_1618181 : Nat := 4983230072969 + 3 ^ 40 * 1618181 * 2
def baseEnd_1618181 : Nat := 830904638973238593095627

theorem tailTrace_1618181 : CollatzResearch.WordTrace tailWord_1618181 prefixEnd_1618181 830904638973238593095627 := by
  unfold tailWord_1618181
  simp only [CollatzResearch.WordTrace]
  refine ⟨59019909750614075157502397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39346606500409383438334931 59019909750614075157502397)
  ·
    refine ⟨22132466156480278184063399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59019909750614075157502397 22132466156480278184063399)
    ·
      refine ⟨33198699234720417276095099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22132466156480278184063399 33198699234720417276095099)
      ·
        refine ⟨49798048852080625914142649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33198699234720417276095099 49798048852080625914142649)
        ·
          refine ⟨37348536639060469435606987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49798048852080625914142649 37348536639060469435606987)
          ·
            refine ⟨56022804958590704153410481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37348536639060469435606987 56022804958590704153410481)
            ·
              refine ⟨42017103718943028115057861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56022804958590704153410481 42017103718943028115057861)
              ·
                refine ⟨7878206947301817771573349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42017103718943028115057861 7878206947301817771573349)
                ·
                  refine ⟨1477163802619090832170003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7878206947301817771573349 1477163802619090832170003)
                  ·
                    refine ⟨2215745703928636248255005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1477163802619090832170003 2215745703928636248255005)
                    ·
                      refine ⟨830904638973238593095627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2215745703928636248255005 830904638973238593095627)
                      ·
                        rfl

theorem cell23_1618181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 1, 3].length) (baseStart_1618181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618181 prefixEnd_1618181 := by exact prefixLift 1618181
  have htrace : WordTrace (prefixWord ++ tailWord_1618181) baseStart_1618181 baseEnd_1618181 := by
    simpa [prefixWord, tailWord_1618181, baseEnd_1618181] using wordTrace_append hprefix tailTrace_1618181
  have hstable : (prefixWord ++ tailWord_1618181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618181).length < 2 ^ (prefixWord ++ tailWord_1618181).sum := by decide
  have hdescent : baseEnd_1618181 < baseStart_1618181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618199 : List Nat := [1, 1, 3, 4, 1, 4, 2, 2, 1, 2, 2]
def baseStart_1618199 : Nat := 118140960795 + 1618199 * 2 ^ 59
def prefixEnd_1618199 : Nat := 4983230072969 + 3 ^ 40 * 1618199 * 2
def baseEnd_1618199 : Nat := 830913881625019522670545

theorem tailTrace_1618199 : CollatzResearch.WordTrace tailWord_1618199 prefixEnd_1618199 830913881625019522670545 := by
  unfold tailWord_1618199
  simp only [CollatzResearch.WordTrace]
  refine ⟨59020566264548864231657651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39347044176365909487771767 59020566264548864231657651)
  ·
    refine ⟨88530849396823296347486477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59020566264548864231657651 88530849396823296347486477)
    ·
      refine ⟨33199068523808736130307429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88530849396823296347486477 33199068523808736130307429)
      ·
        refine ⟨6224825348214138024432643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33199068523808736130307429 6224825348214138024432643)
        ·
          refine ⟨9337238022321207036648965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6224825348214138024432643 9337238022321207036648965)
          ·
            refine ⟨1750732129185226319371681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9337238022321207036648965 1750732129185226319371681)
            ·
              refine ⟨1313049096888919739528761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1750732129185226319371681 1313049096888919739528761)
              ·
                refine ⟨984786822666689804646571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1313049096888919739528761 984786822666689804646571)
                ·
                  refine ⟨1477180234000034706969857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 984786822666689804646571 1477180234000034706969857)
                  ·
                    refine ⟨1107885175500026030227393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1477180234000034706969857 1107885175500026030227393)
                    ·
                      refine ⟨830913881625019522670545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1107885175500026030227393 830913881625019522670545)
                      ·
                        rfl

theorem cell23_1618199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_1618199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618199 prefixEnd_1618199 := by exact prefixLift 1618199
  have htrace : WordTrace (prefixWord ++ tailWord_1618199) baseStart_1618199 baseEnd_1618199 := by
    simpa [prefixWord, tailWord_1618199, baseEnd_1618199] using wordTrace_append hprefix tailTrace_1618199
  have hstable : (prefixWord ++ tailWord_1618199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618199).length < 2 ^ (prefixWord ++ tailWord_1618199).sum := by decide
  have hdescent : baseEnd_1618199 < baseStart_1618199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618208 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 3, 3, 2]
def baseStart_1618208 : Nat := 118140960795 + 1618208 * 2 ^ 59
def prefixEnd_1618208 : Nat := 4983230072969 + 3 ^ 40 * 1618208 * 2
def baseEnd_1618208 : Nat := 830918502950909987458003

theorem tailTrace_1618208 : CollatzResearch.WordTrace tailWord_1618208 prefixEnd_1618208 830918502950909987458003 := by
  unfold tailWord_1618208
  simp only [CollatzResearch.WordTrace]
  refine ⟨29510447260758129384367639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39347263014344172512490185 29510447260758129384367639)
  ·
    refine ⟨44265670891137194076551459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29510447260758129384367639 44265670891137194076551459)
    ·
      refine ⟨66398506336705791114827189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44265670891137194076551459 66398506336705791114827189)
      ·
        refine ⟨6224859969066167917015049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66398506336705791114827189 6224859969066167917015049)
        ·
          refine ⟨4668644976799625937761287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6224859969066167917015049 4668644976799625937761287)
          ·
            refine ⟨7002967465199438906641931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4668644976799625937761287 7002967465199438906641931)
            ·
              refine ⟨10504451197799158359962897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7002967465199438906641931 10504451197799158359962897)
              ·
                refine ⟨7878338398349368769972173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10504451197799158359962897 7878338398349368769972173)
                ·
                  refine ⟨2954376899381013288739565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7878338398349368769972173 2954376899381013288739565)
                  ·
                    refine ⟨1107891337267879983277337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2954376899381013288739565 1107891337267879983277337)
                    ·
                      refine ⟨830918502950909987458003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1107891337267879983277337 830918502950909987458003)
                      ·
                        rfl

theorem cell23_1618208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_1618208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618208 prefixEnd_1618208 := by exact prefixLift 1618208
  have htrace : WordTrace (prefixWord ++ tailWord_1618208) baseStart_1618208 baseEnd_1618208 := by
    simpa [prefixWord, tailWord_1618208, baseEnd_1618208] using wordTrace_append hprefix tailTrace_1618208
  have hstable : (prefixWord ++ tailWord_1618208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618208).length < 2 ^ (prefixWord ++ tailWord_1618208).sum := by decide
  have hdescent : baseEnd_1618208 < baseStart_1618208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618224 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 5]
def baseStart_1618224 : Nat := 118140960795 + 1618224 * 2 ^ 59
def prefixEnd_1618224 : Nat := 4983230072969 + 3 ^ 40 * 1618224 * 2
def baseEnd_1618224 : Nat := 830926718641381924857929

theorem tailTrace_1618224 : CollatzResearch.WordTrace tailWord_1618224 prefixEnd_1618224 830926718641381924857929 := by
  unfold tailWord_1618224
  simp only [CollatzResearch.WordTrace]
  refine ⟨29510739044729146750658863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39347652059638862334211817 29510739044729146750658863)
  ·
    refine ⟨44266108567093720125988295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29510739044729146750658863 44266108567093720125988295)
    ·
      refine ⟨66399162850640580188982443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44266108567093720125988295 66399162850640580188982443)
      ·
        refine ⟨99598744275960870283473665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66399162850640580188982443 99598744275960870283473665)
        ·
          refine ⟨74699058206970652712605249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99598744275960870283473665 74699058206970652712605249)
          ·
            refine ⟨56024293655227989534453937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74699058206970652712605249 56024293655227989534453937)
            ·
              refine ⟨42018220241420992150840453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56024293655227989534453937 42018220241420992150840453)
              ·
                refine ⟨7878416295266436028282585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42018220241420992150840453 7878416295266436028282585)
                ·
                  refine ⟨5908812221449827021211939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7878416295266436028282585 5908812221449827021211939)
                  ·
                    refine ⟨8863218332174740531817909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5908812221449827021211939 8863218332174740531817909)
                    ·
                      refine ⟨830926718641381924857929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8863218332174740531817909 830926718641381924857929)
                      ·
                        rfl

theorem cell23_1618224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_1618224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618224 prefixEnd_1618224 := by exact prefixLift 1618224
  have htrace : WordTrace (prefixWord ++ tailWord_1618224) baseStart_1618224 baseEnd_1618224 := by
    simpa [prefixWord, tailWord_1618224, baseEnd_1618224] using wordTrace_append hprefix tailTrace_1618224
  have hstable : (prefixWord ++ tailWord_1618224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618224).length < 2 ^ (prefixWord ++ tailWord_1618224).sum := by decide
  have hdescent : baseEnd_1618224 < baseStart_1618224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618254 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_1618254 : Nat := 118140960795 + 1618254 * 2 ^ 59
def prefixEnd_1618254 : Nat := 4983230072969 + 3 ^ 40 * 1618254 * 2
def baseEnd_1618254 : Nat := 830942123061016807482791

theorem tailTrace_1618254 : CollatzResearch.WordTrace tailWord_1618254 prefixEnd_1618254 830942123061016807482791 := by
  unfold tailWord_1618254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7377821534918701078113727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39348381519566405749939877 7377821534918701078113727)
  ·
    refine ⟨11066732302378051617170591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7377821534918701078113727 11066732302378051617170591)
    ·
      refine ⟨16600098453567077425755887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11066732302378051617170591 16600098453567077425755887)
      ·
        refine ⟨24900147680350616138633831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16600098453567077425755887 24900147680350616138633831)
        ·
          refine ⟨37350221520525924207950747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24900147680350616138633831 37350221520525924207950747)
          ·
            refine ⟨56025332280788886311926121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37350221520525924207950747 56025332280788886311926121)
            ·
              refine ⟨42018999210591664733944591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56025332280788886311926121 42018999210591664733944591)
              ·
                refine ⟨63028498815887497100916887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42018999210591664733944591 63028498815887497100916887)
                ·
                  refine ⟨94542748223831245651375331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63028498815887497100916887 94542748223831245651375331)
                  ·
                    refine ⟨141814122335746868477062997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94542748223831245651375331 141814122335746868477062997)
                    ·
                      refine ⟨830942123061016807482791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 141814122335746868477062997 830942123061016807482791)
                      ·
                        rfl

theorem cell23_1618254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_1618254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618254 prefixEnd_1618254 := by exact prefixLift 1618254
  have htrace : WordTrace (prefixWord ++ tailWord_1618254) baseStart_1618254 baseEnd_1618254 := by
    simpa [prefixWord, tailWord_1618254, baseEnd_1618254] using wordTrace_append hprefix tailTrace_1618254
  have hstable : (prefixWord ++ tailWord_1618254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618254).length < 2 ^ (prefixWord ++ tailWord_1618254).sum := by decide
  have hdescent : baseEnd_1618254 < baseStart_1618254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618271 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 3]
def baseStart_1618271 : Nat := 118140960795 + 1618271 * 2 ^ 59
def prefixEnd_1618271 : Nat := 4983230072969 + 3 ^ 40 * 1618271 * 2
def baseEnd_1618271 : Nat := 830950852232143240970213

theorem tailTrace_1618271 : CollatzResearch.WordTrace tailWord_1618271 prefixEnd_1618271 830950852232143240970213 := by
  unfold tailWord_1618271
  simp only [CollatzResearch.WordTrace]
  refine ⟨59023192320288020528278667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39348794880192013685519111 59023192320288020528278667)
  ·
    refine ⟨88534788480432030792418001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59023192320288020528278667 88534788480432030792418001)
    ·
      refine ⟨66401091360324023094313501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88534788480432030792418001 66401091360324023094313501)
      ·
        refine ⟨24900409260121508660367563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66401091360324023094313501 24900409260121508660367563)
        ·
          refine ⟨37350613890182262990551345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24900409260121508660367563 37350613890182262990551345)
          ·
            refine ⟨28012960417636697242913509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37350613890182262990551345 28012960417636697242913509)
            ·
              refine ⟨5252430078306880733046283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28012960417636697242913509 5252430078306880733046283)
              ·
                refine ⟨7878645117460321099569425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5252430078306880733046283 7878645117460321099569425)
                ·
                  refine ⟨5908983838095240824677069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7878645117460321099569425 5908983838095240824677069)
                  ·
                    refine ⟨2215868939285715309253901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5908983838095240824677069 2215868939285715309253901)
                    ·
                      refine ⟨830950852232143240970213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2215868939285715309253901 830950852232143240970213)
                      ·
                        rfl

theorem cell23_1618271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_1618271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618271 prefixEnd_1618271 := by exact prefixLift 1618271
  have htrace : WordTrace (prefixWord ++ tailWord_1618271) baseStart_1618271 baseEnd_1618271 := by
    simpa [prefixWord, tailWord_1618271, baseEnd_1618271] using wordTrace_append hprefix tailTrace_1618271
  have hstable : (prefixWord ++ tailWord_1618271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618271).length < 2 ^ (prefixWord ++ tailWord_1618271).sum := by decide
  have hdescent : baseEnd_1618271 < baseStart_1618271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618272 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 1, 4, 2]
def baseStart_1618272 : Nat := 118140960795 + 1618272 * 2 ^ 59
def prefixEnd_1618272 : Nat := 4983230072969 + 3 ^ 40 * 1618272 * 2
def baseEnd_1618272 : Nat := 830951365712797737057709

theorem tailTrace_1618272 : CollatzResearch.WordTrace tailWord_1618272 prefixEnd_1618272 830951365712797737057709 := by
  unfold tailWord_1618272
  simp only [CollatzResearch.WordTrace]
  refine ⟨29511614396642198849532535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39348819195522931799376713 29511614396642198849532535)
  ·
    refine ⟨44267421594963298274298803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29511614396642198849532535 44267421594963298274298803)
    ·
      refine ⟨66401132392444947411448205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44267421594963298274298803 66401132392444947411448205)
      ·
        refine ⟨24900424647166855279293077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66401132392444947411448205 24900424647166855279293077)
        ·
          refine ⟨1167207405335946341216863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24900424647166855279293077 1167207405335946341216863)
          ·
            refine ⟨1750811108003919511825295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167207405335946341216863 1750811108003919511825295)
            ·
              refine ⟨2626216662005879267737943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1750811108003919511825295 2626216662005879267737943)
              ·
                refine ⟨3939324993008818901606915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2626216662005879267737943 3939324993008818901606915)
                ·
                  refine ⟨5908987489513228352410373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3939324993008818901606915 5908987489513228352410373)
                  ·
                    refine ⟨1107935154283730316076945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5908987489513228352410373 1107935154283730316076945)
                    ·
                      refine ⟨830951365712797737057709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1107935154283730316076945 830951365712797737057709)
                      ·
                        rfl

theorem cell23_1618272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_1618272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618272 prefixEnd_1618272 := by exact prefixLift 1618272
  have htrace : WordTrace (prefixWord ++ tailWord_1618272) baseStart_1618272 baseEnd_1618272 := by
    simpa [prefixWord, tailWord_1618272, baseEnd_1618272] using wordTrace_append hprefix tailTrace_1618272
  have hstable : (prefixWord ++ tailWord_1618272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618272).length < 2 ^ (prefixWord ++ tailWord_1618272).sum := by decide
  have hdescent : baseEnd_1618272 < baseStart_1618272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618318 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1618318 : Nat := 118140960795 + 1618318 * 2 ^ 59
def prefixEnd_1618318 : Nat := 4983230072969 + 3 ^ 40 * 1618318 * 2
def baseEnd_1618318 : Nat := 830974985822904557082497

theorem tailTrace_1618318 : CollatzResearch.WordTrace tailWord_1618318 prefixEnd_1618318 830974985822904557082497 := by
  unfold tailWord_1618318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7378113318889718444404951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39349937700745165036826405 7378113318889718444404951)
  ·
    refine ⟨11067169978334577666607427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7378113318889718444404951 11067169978334577666607427)
    ·
      refine ⟨16600754967501866499911141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11067169978334577666607427 16600754967501866499911141)
      ·
        refine ⟨3112641556406599968733339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16600754967501866499911141 3112641556406599968733339)
        ·
          refine ⟨4668962334609899953100009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3112641556406599968733339 4668962334609899953100009)
          ·
            refine ⟨3501721750957424964825007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4668962334609899953100009 3501721750957424964825007)
            ·
              refine ⟨5252582626436137447237511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3501721750957424964825007 5252582626436137447237511)
              ·
                refine ⟨7878873939654206170856267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5252582626436137447237511 7878873939654206170856267)
                ·
                  refine ⟨11818310909481309256284401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7878873939654206170856267 11818310909481309256284401)
                  ·
                    refine ⟨8863733182110981942213301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11818310909481309256284401 8863733182110981942213301)
                    ·
                      refine ⟨830974985822904557082497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8863733182110981942213301 830974985822904557082497)
                      ·
                        rfl

theorem cell23_1618318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1618318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618318 prefixEnd_1618318 := by exact prefixLift 1618318
  have htrace : WordTrace (prefixWord ++ tailWord_1618318) baseStart_1618318 baseEnd_1618318 := by
    simpa [prefixWord, tailWord_1618318, baseEnd_1618318] using wordTrace_append hprefix tailTrace_1618318
  have hstable : (prefixWord ++ tailWord_1618318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618318).length < 2 ^ (prefixWord ++ tailWord_1618318).sum := by decide
  have hdescent : baseEnd_1618318 < baseStart_1618318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618338 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_1618338 : Nat := 118140960795 + 1618338 * 2 ^ 59
def prefixEnd_1618338 : Nat := 4983230072969 + 3 ^ 40 * 1618338 * 2
def baseEnd_1618338 : Nat := 276995085145331492944135

theorem tailTrace_1618338 : CollatzResearch.WordTrace tailWord_1618338 prefixEnd_1618338 276995085145331492944135 := by
  unfold tailWord_1618338
  simp only [CollatzResearch.WordTrace]
  refine ⟨14756409002761322742741917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39350424007363527313978445 14756409002761322742741917)
  ·
    refine ⟨5533653376035496028528219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14756409002761322742741917 5533653376035496028528219)
    ·
      refine ⟨8300480064053244042792329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5533653376035496028528219 8300480064053244042792329)
      ·
        refine ⟨6225360048039933032094247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8300480064053244042792329 6225360048039933032094247)
        ·
          refine ⟨9338040072059899548141371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6225360048039933032094247 9338040072059899548141371)
          ·
            refine ⟨14007060108089849322212057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9338040072059899548141371 14007060108089849322212057)
            ·
              refine ⟨10505295081067386991659043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14007060108089849322212057 10505295081067386991659043)
              ·
                refine ⟨15757942621601080487488565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10505295081067386991659043 15757942621601080487488565)
                ·
                  refine ⟨1477307120775101295702053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15757942621601080487488565 1477307120775101295702053)
                  ·
                    refine ⟨276995085145331492944135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1477307120775101295702053 276995085145331492944135)
                    ·
                      rfl

theorem cell23_1618338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_1618338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618338 prefixEnd_1618338 := by exact prefixLift 1618338
  have htrace : WordTrace (prefixWord ++ tailWord_1618338) baseStart_1618338 baseEnd_1618338 := by
    simpa [prefixWord, tailWord_1618338, baseEnd_1618338] using wordTrace_append hprefix tailTrace_1618338
  have hstable : (prefixWord ++ tailWord_1618338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618338).length < 2 ^ (prefixWord ++ tailWord_1618338).sum := by decide
  have hdescent : baseEnd_1618338 < baseStart_1618338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618411 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 1, 6]
def baseStart_1618411 : Nat := 118140960795 + 1618411 * 2 ^ 59
def prefixEnd_1618411 : Nat := 4983230072969 + 3 ^ 40 * 1618411 * 2
def baseEnd_1618411 : Nat := 277007579841257564406523

theorem tailTrace_1618411 : CollatzResearch.WordTrace tailWord_1618411 prefixEnd_1618411 277007579841257564406523 := by
  unfold tailWord_1618411
  simp only [CollatzResearch.WordTrace]
  refine ⟨59028298539780824438375087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39352199026520549625583391 59028298539780824438375087)
  ·
    refine ⟨88542447809671236657562631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59028298539780824438375087 88542447809671236657562631)
    ·
      refine ⟨132813671714506854986343947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88542447809671236657562631 132813671714506854986343947)
      ·
        refine ⟨199220507571760282479515921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132813671714506854986343947 199220507571760282479515921)
        ·
          refine ⟨149415380678820211859636941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199220507571760282479515921 149415380678820211859636941)
          ·
            refine ⟨56030767754557579447363853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149415380678820211859636941 56030767754557579447363853)
            ·
              refine ⟨21011537907959092292761445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56030767754557579447363853 21011537907959092292761445)
              ·
                refine ⟨3939663357742329804892771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21011537907959092292761445 3939663357742329804892771)
                ·
                  refine ⟨5909495036613494707339157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3939663357742329804892771 5909495036613494707339157)
                  ·
                    refine ⟨277007579841257564406523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5909495036613494707339157 277007579841257564406523)
                    ·
                      rfl

theorem cell23_1618411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 6].length) (baseStart_1618411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618411 prefixEnd_1618411 := by exact prefixLift 1618411
  have htrace : WordTrace (prefixWord ++ tailWord_1618411) baseStart_1618411 baseEnd_1618411 := by
    simpa [prefixWord, tailWord_1618411, baseEnd_1618411] using wordTrace_append hprefix tailTrace_1618411
  have hstable : (prefixWord ++ tailWord_1618411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618411).length < 2 ^ (prefixWord ++ tailWord_1618411).sum := by decide
  have hdescent : baseEnd_1618411 < baseStart_1618411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618412 : List Nat := [2, 2, 1, 1, 2, 1, 6, 3, 1, 1, 3]
def baseStart_1618412 : Nat := 118140960795 + 1618412 * 2 ^ 59
def prefixEnd_1618412 : Nat := 4983230072969 + 3 ^ 40 * 1618412 * 2
def baseEnd_1618412 : Nat := 831023253004427189307065

theorem tailTrace_1618412 : CollatzResearch.WordTrace tailWord_1618412 prefixEnd_1618412 831023253004427189307065 := by
  unfold tailWord_1618412
  simp only [CollatzResearch.WordTrace]
  refine ⟨29514167506388600804580745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39352223341851467739440993 29514167506388600804580745)
  ·
    refine ⟨22135625629791450603435559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29514167506388600804580745 22135625629791450603435559)
    ·
      refine ⟨33203438444687175905153339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22135625629791450603435559 33203438444687175905153339)
      ·
        refine ⟨49805157667030763857730009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33203438444687175905153339 49805157667030763857730009)
        ·
          refine ⟨37353868250273072893297507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49805157667030763857730009 37353868250273072893297507)
          ·
            refine ⟨56030802375409609339946261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37353868250273072893297507 56030802375409609339946261)
            ·
              refine ⟨2626443861347325437809981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56030802375409609339946261 2626443861347325437809981)
              ·
                refine ⟨984916448005247039178743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2626443861347325437809981 984916448005247039178743)
                ·
                  refine ⟨1477374672007870558768115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 984916448005247039178743 1477374672007870558768115)
                  ·
                    refine ⟨2216062008011805838152173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1477374672007870558768115 2216062008011805838152173)
                    ·
                      refine ⟨831023253004427189307065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2216062008011805838152173 831023253004427189307065)
                      ·
                        rfl

theorem cell23_1618412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 1, 1, 3].length) (baseStart_1618412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618412 prefixEnd_1618412 := by exact prefixLift 1618412
  have htrace : WordTrace (prefixWord ++ tailWord_1618412) baseStart_1618412 baseEnd_1618412 := by
    simpa [prefixWord, tailWord_1618412, baseEnd_1618412] using wordTrace_append hprefix tailTrace_1618412
  have hstable : (prefixWord ++ tailWord_1618412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618412).length < 2 ^ (prefixWord ++ tailWord_1618412).sum := by decide
  have hdescent : baseEnd_1618412 < baseStart_1618412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618431 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 6]
def baseStart_1618431 : Nat := 118140960795 + 1618431 * 2 ^ 59
def prefixEnd_1618431 : Nat := 4983230072969 + 3 ^ 40 * 1618431 * 2
def baseEnd_1618431 : Nat := 831033009136862614969477

theorem tailTrace_1618431 : CollatzResearch.WordTrace tailWord_1618431 prefixEnd_1618431 831033009136862614969477 := by
  unfold tailWord_1618431
  simp only [CollatzResearch.WordTrace]
  refine ⟨59029027999708367854103147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39352685333138911902735431 59029027999708367854103147)
  ·
    refine ⟨88543541999562551781154721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59029027999708367854103147 88543541999562551781154721)
    ·
      refine ⟨66407656499671913835866041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88543541999562551781154721 66407656499671913835866041)
      ·
        refine ⟨49805742374753935376899531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66407656499671913835866041 49805742374753935376899531)
        ·
          refine ⟨74708613562130903065349297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49805742374753935376899531 74708613562130903065349297)
          ·
            refine ⟨56031460171598177299011973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74708613562130903065349297 56031460171598177299011973)
            ·
              refine ⟨10505898782174658243564745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56031460171598177299011973 10505898782174658243564745)
              ·
                refine ⟨7879424086630993682673559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10505898782174658243564745 7879424086630993682673559)
                ·
                  refine ⟨11819136129946490524010339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7879424086630993682673559 11819136129946490524010339)
                  ·
                    refine ⟨17728704194919735786015509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11819136129946490524010339 17728704194919735786015509)
                    ·
                      refine ⟨831033009136862614969477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17728704194919735786015509 831033009136862614969477)
                      ·
                        rfl

theorem cell23_1618431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_1618431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618431 prefixEnd_1618431 := by exact prefixLift 1618431
  have htrace : WordTrace (prefixWord ++ tailWord_1618431) baseStart_1618431 baseEnd_1618431 := by
    simpa [prefixWord, tailWord_1618431, baseEnd_1618431] using wordTrace_append hprefix tailTrace_1618431
  have hstable : (prefixWord ++ tailWord_1618431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618431).length < 2 ^ (prefixWord ++ tailWord_1618431).sum := by decide
  have hdescent : baseEnd_1618431 < baseStart_1618431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618452 : List Nat := [2, 4, 3, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_1618452 : Nat := 118140960795 + 1618452 * 2 ^ 59
def prefixEnd_1618452 : Nat := 4983230072969 + 3 ^ 40 * 1618452 * 2
def baseEnd_1618452 : Nat := 831043792230607032806881

theorem tailTrace_1618452 : CollatzResearch.WordTrace tailWord_1618452 prefixEnd_1618452 831043792230607032806881 := by
  unfold tailWord_1618452
  simp only [CollatzResearch.WordTrace]
  refine ⟨29514896966316144220308805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39353195955088192293745073 29514896966316144220308805)
  ·
    refine ⟨5534043181184277041307901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29514896966316144220308805 5534043181184277041307901)
    ·
      refine ⟨2075266192944103890490463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5534043181184277041307901 2075266192944103890490463)
      ·
        refine ⟨3112899289416155835735695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2075266192944103890490463 3112899289416155835735695)
        ·
          refine ⟨4669348934124233753603543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3112899289416155835735695 4669348934124233753603543)
          ·
            refine ⟨7004023401186350630405315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4669348934124233753603543 7004023401186350630405315)
            ·
              refine ⟨10506035101779525945607973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7004023401186350630405315 10506035101779525945607973)
              ·
                refine ⟨1969881581583661114801495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10506035101779525945607973 1969881581583661114801495)
                ·
                  refine ⟨2954822372375491672202243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1969881581583661114801495 2954822372375491672202243)
                  ·
                    refine ⟨4432233558563237508303365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2954822372375491672202243 4432233558563237508303365)
                    ·
                      refine ⟨831043792230607032806881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4432233558563237508303365 831043792230607032806881)
                      ·
                        rfl

theorem cell23_1618452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_1618452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618452 prefixEnd_1618452 := by exact prefixLift 1618452
  have htrace : WordTrace (prefixWord ++ tailWord_1618452) baseStart_1618452 baseEnd_1618452 := by
    simpa [prefixWord, tailWord_1618452, baseEnd_1618452] using wordTrace_append hprefix tailTrace_1618452
  have hstable : (prefixWord ++ tailWord_1618452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618452).length < 2 ^ (prefixWord ++ tailWord_1618452).sum := by decide
  have hdescent : baseEnd_1618452 < baseStart_1618452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618458 : List Nat := [3, 1, 1, 3, 1, 1, 6, 7]
def baseStart_1618458 : Nat := 118140960795 + 1618458 * 2 ^ 59
def prefixEnd_1618458 : Nat := 4983230072969 + 3 ^ 40 * 1618458 * 2
def baseEnd_1618458 : Nat := 30779513819056815160439

theorem tailTrace_1618458 : CollatzResearch.WordTrace tailWord_1618458 prefixEnd_1618458 30779513819056815160439 := by
  unfold tailWord_1618458
  simp only [CollatzResearch.WordTrace]
  refine ⟨14757503192652637866334007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39353341847073700976890685 14757503192652637866334007)
  ·
    refine ⟨22136254788978956799501011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14757503192652637866334007 22136254788978956799501011)
    ·
      refine ⟨33204382183468435199251517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22136254788978956799501011 33204382183468435199251517)
      ·
        refine ⟨12451643318800663199719319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33204382183468435199251517 12451643318800663199719319)
        ·
          refine ⟨18677464978200994799578979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12451643318800663199719319 18677464978200994799578979)
          ·
            refine ⟨28016197467301492199368469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18677464978200994799578979 28016197467301492199368469)
            ·
              refine ⟨1313259256279757446845397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28016197467301492199368469 1313259256279757446845397)
              ·
                refine ⟨30779513819056815160439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1313259256279757446845397 30779513819056815160439)
                ·
                  rfl

theorem cell23_1618458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 7].length) (baseStart_1618458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618458 prefixEnd_1618458 := by exact prefixLift 1618458
  have htrace : WordTrace (prefixWord ++ tailWord_1618458) baseStart_1618458 baseEnd_1618458 := by
    simpa [prefixWord, tailWord_1618458, baseEnd_1618458] using wordTrace_append hprefix tailTrace_1618458
  have hstable : (prefixWord ++ tailWord_1618458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618458).length < 2 ^ (prefixWord ++ tailWord_1618458).sum := by decide
  have hdescent : baseEnd_1618458 < baseStart_1618458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618469 : List Nat := [1, 3, 1, 2, 2, 1, 5, 3, 1, 2, 2]
def baseStart_1618469 : Nat := 118140960795 + 1618469 * 2 ^ 59
def prefixEnd_1618469 : Nat := 4983230072969 + 3 ^ 40 * 1618469 * 2
def baseEnd_1618469 : Nat := 831052521401733466294303

theorem tailTrace_1618469 : CollatzResearch.WordTrace tailWord_1618469 prefixEnd_1618469 831052521401733466294303 := by
  unfold tailWord_1618469
  simp only [CollatzResearch.WordTrace]
  refine ⟨59030413973570700343986461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39353609315713800229324307 59030413973570700343986461)
  ·
    refine ⟨22136405240089012628994923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59030413973570700343986461 22136405240089012628994923)
    ·
      refine ⟨33204607860133518943492385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22136405240089012628994923 33204607860133518943492385)
      ·
        refine ⟨24903455895100139207619289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33204607860133518943492385 24903455895100139207619289)
        ·
          refine ⟨18677591921325104405714467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24903455895100139207619289 18677591921325104405714467)
          ·
            refine ⟨28016387881987656608571701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18677591921325104405714467 28016387881987656608571701)
            ·
              refine ⟨2626536363936342807053597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28016387881987656608571701 2626536363936342807053597)
              ·
                refine ⟨984951136476128552645099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2626536363936342807053597 984951136476128552645099)
                ·
                  refine ⟨1477426704714192828967649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 984951136476128552645099 1477426704714192828967649)
                  ·
                    refine ⟨1108070028535644621725737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1477426704714192828967649 1108070028535644621725737)
                    ·
                      refine ⟨831052521401733466294303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1108070028535644621725737 831052521401733466294303)
                      ·
                        rfl

theorem cell23_1618469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_1618469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618469 prefixEnd_1618469 := by exact prefixLift 1618469
  have htrace : WordTrace (prefixWord ++ tailWord_1618469) baseStart_1618469 baseEnd_1618469 := by
    simpa [prefixWord, tailWord_1618469, baseEnd_1618469] using wordTrace_append hprefix tailTrace_1618469
  have hstable : (prefixWord ++ tailWord_1618469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618469).length < 2 ^ (prefixWord ++ tailWord_1618469).sum := by decide
  have hdescent : baseEnd_1618469 < baseStart_1618469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618472 : List Nat := [2, 1, 5, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_1618472 : Nat := 118140960795 + 1618472 * 2 ^ 59
def prefixEnd_1618472 : Nat := 4983230072969 + 3 ^ 40 * 1618472 * 2
def baseEnd_1618472 : Nat := 831054061843696954556789

theorem tailTrace_1618472 : CollatzResearch.WordTrace tailWord_1618472 prefixEnd_1618472 831054061843696954556789 := by
  unfold tailWord_1618472
  simp only [CollatzResearch.WordTrace]
  refine ⟨29515261696279915928172835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39353682261706554570897113 29515261696279915928172835)
  ·
    refine ⟨44272892544419873892259253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29515261696279915928172835 44272892544419873892259253)
    ·
      refine ⟨4150583676039363177399305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44272892544419873892259253 4150583676039363177399305)
      ·
        refine ⟨3112937757029522383049479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4150583676039363177399305 3112937757029522383049479)
        ·
          refine ⟨4669406635544283574574219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3112937757029522383049479 4669406635544283574574219)
          ·
            refine ⟨7004109953316425361861329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4669406635544283574574219 7004109953316425361861329)
            ·
              refine ⟨5253082464987319021395997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7004109953316425361861329 5253082464987319021395997)
              ·
                refine ⟨1969905924370244633023499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5253082464987319021395997 1969905924370244633023499)
                ·
                  refine ⟨2954858886555366949535249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1969905924370244633023499 2954858886555366949535249)
                  ·
                    refine ⟨2216144164916525212151437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2954858886555366949535249 2216144164916525212151437)
                    ·
                      refine ⟨831054061843696954556789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2216144164916525212151437 831054061843696954556789)
                      ·
                        rfl

theorem cell23_1618472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_1618472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618472 prefixEnd_1618472 := by exact prefixLift 1618472
  have htrace : WordTrace (prefixWord ++ tailWord_1618472) baseStart_1618472 baseEnd_1618472 := by
    simpa [prefixWord, tailWord_1618472, baseEnd_1618472] using wordTrace_append hprefix tailTrace_1618472
  have hstable : (prefixWord ++ tailWord_1618472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618472).length < 2 ^ (prefixWord ++ tailWord_1618472).sum := by decide
  have hdescent : baseEnd_1618472 < baseStart_1618472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618485 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_1618485 : Nat := 118140960795 + 1618485 * 2 ^ 59
def prefixEnd_1618485 : Nat := 4983230072969 + 3 ^ 40 * 1618485 * 2
def baseEnd_1618485 : Nat := 831060737092205403694229

theorem tailTrace_1618485 : CollatzResearch.WordTrace tailWord_1618485 prefixEnd_1618485 831060737092205403694229 := by
  unfold tailWord_1618485
  simp only [CollatzResearch.WordTrace]
  refine ⟨59030997541512735076568909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39353998361008490051045939 59030997541512735076568909)
  ·
    refine ⟨22136624078067275653713341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59030997541512735076568909 22136624078067275653713341)
    ·
      refine ⟨8301234029275228370142503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22136624078067275653713341 8301234029275228370142503)
      ·
        refine ⟨12451851043912842555213755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8301234029275228370142503 12451851043912842555213755)
        ·
          refine ⟨18677776565869263832820633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12451851043912842555213755 18677776565869263832820633)
          ·
            refine ⟨14008332424401947874615475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18677776565869263832820633 14008332424401947874615475)
            ·
              refine ⟨21012498636602921811923213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14008332424401947874615475 21012498636602921811923213)
              ·
                refine ⟨7879686988726095679471205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21012498636602921811923213 7879686988726095679471205)
                ·
                  refine ⟨1477441310386142939900851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7879686988726095679471205 1477441310386142939900851)
                  ·
                    refine ⟨2216161965579214409851277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1477441310386142939900851 2216161965579214409851277)
                    ·
                      refine ⟨831060737092205403694229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2216161965579214409851277 831060737092205403694229)
                      ·
                        rfl

theorem cell23_1618485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_1618485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618485 prefixEnd_1618485 := by exact prefixLift 1618485
  have htrace : WordTrace (prefixWord ++ tailWord_1618485) baseStart_1618485 baseEnd_1618485 := by
    simpa [prefixWord, tailWord_1618485, baseEnd_1618485] using wordTrace_append hprefix tailTrace_1618485
  have hstable : (prefixWord ++ tailWord_1618485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618485).length < 2 ^ (prefixWord ++ tailWord_1618485).sum := by decide
  have hdescent : baseEnd_1618485 < baseStart_1618485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618486 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_1618486 : Nat := 118140960795 + 1618486 * 2 ^ 59
def prefixEnd_1618486 : Nat := 4983230072969 + 3 ^ 40 * 1618486 * 2
def baseEnd_1618486 : Nat := 831061250572859899781725

theorem tailTrace_1618486 : CollatzResearch.WordTrace tailWord_1618486 prefixEnd_1618486 831061250572859899781725 := by
  unfold tailWord_1618486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3689439625906819515459707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39354022676339408164903541 3689439625906819515459707)
  ·
    refine ⟨5534159438860229273189561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3689439625906819515459707 5534159438860229273189561)
    ·
      refine ⟨4150619579145171954892171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5534159438860229273189561 4150619579145171954892171)
      ·
        refine ⟨6225929368717757932338257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4150619579145171954892171 6225929368717757932338257)
        ·
          refine ⟨4669447026538318449253693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6225929368717757932338257 4669447026538318449253693)
          ·
            refine ⟨1751042634951869418470135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4669447026538318449253693 1751042634951869418470135)
            ·
              refine ⟨2626563952427804127705203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1751042634951869418470135 2626563952427804127705203)
              ·
                refine ⟨3939845928641706191557805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2626563952427804127705203 3939845928641706191557805)
                ·
                  refine ⟨1477442223240639821834177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3939845928641706191557805 1477442223240639821834177)
                  ·
                    refine ⟨1108081667430479866375633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1477442223240639821834177 1108081667430479866375633)
                    ·
                      refine ⟨831061250572859899781725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1108081667430479866375633 831061250572859899781725)
                      ·
                        rfl

theorem cell23_1618486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_1618486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618486 prefixEnd_1618486 := by exact prefixLift 1618486
  have htrace : WordTrace (prefixWord ++ tailWord_1618486) baseStart_1618486 baseEnd_1618486 := by
    simpa [prefixWord, tailWord_1618486, baseEnd_1618486] using wordTrace_append hprefix tailTrace_1618486
  have hstable : (prefixWord ++ tailWord_1618486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618486).length < 2 ^ (prefixWord ++ tailWord_1618486).sum := by decide
  have hdescent : baseEnd_1618486 < baseStart_1618486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618495 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 3, 3, 2]
def baseStart_1618495 : Nat := 118140960795 + 1618495 * 2 ^ 59
def prefixEnd_1618495 : Nat := 4983230072969 + 3 ^ 40 * 1618495 * 2
def baseEnd_1618495 : Nat := 831065871898750364569183

theorem tailTrace_1618495 : CollatzResearch.WordTrace tailWord_1618495 prefixEnd_1618495 831065871898750364569183 := by
  unfold tailWord_1618495
  simp only [CollatzResearch.WordTrace]
  refine ⟨59031362271476506784432939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39354241514317671189621959 59031362271476506784432939)
  ·
    refine ⟨88547043407214760176649409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59031362271476506784432939 88547043407214760176649409)
    ·
      refine ⟨66410282555411070132487057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88547043407214760176649409 66410282555411070132487057)
      ·
        refine ⟨49807711916558302599365293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66410282555411070132487057 49807711916558302599365293)
        ·
          refine ⟨18677891968709363474761985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49807711916558302599365293 18677891968709363474761985)
          ·
            refine ⟨14008418976532022606071489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18677891968709363474761985 14008418976532022606071489)
            ·
              refine ⟨10506314232399016954553617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14008418976532022606071489 10506314232399016954553617)
              ·
                refine ⟨7879735674299262715915213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10506314232399016954553617 7879735674299262715915213)
                ·
                  refine ⟨2954900877862223518468205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7879735674299262715915213 2954900877862223518468205)
                  ·
                    refine ⟨1108087829198333819425577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2954900877862223518468205 1108087829198333819425577)
                    ·
                      refine ⟨831065871898750364569183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1108087829198333819425577 831065871898750364569183)
                      ·
                        rfl

theorem cell23_1618495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 3, 2].length) (baseStart_1618495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618495 prefixEnd_1618495 := by exact prefixLift 1618495
  have htrace : WordTrace (prefixWord ++ tailWord_1618495) baseStart_1618495 baseEnd_1618495 := by
    simpa [prefixWord, tailWord_1618495, baseEnd_1618495] using wordTrace_append hprefix tailTrace_1618495
  have hstable : (prefixWord ++ tailWord_1618495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618495).length < 2 ^ (prefixWord ++ tailWord_1618495).sum := by decide
  have hdescent : baseEnd_1618495 < baseStart_1618495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618528 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 5]
def baseStart_1618528 : Nat := 118140960795 + 1618528 * 2 ^ 59
def prefixEnd_1618528 : Nat := 4983230072969 + 3 ^ 40 * 1618528 * 2
def baseEnd_1618528 : Nat := 831082816760348735456531

theorem tailTrace_1618528 : CollatzResearch.WordTrace tailWord_1618528 prefixEnd_1618528 831082816760348735456531 := by
  unfold tailWord_1618528
  simp only [CollatzResearch.WordTrace]
  refine ⟨29516282940178476710192119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39355043920237968946922825 29516282940178476710192119)
  ·
    refine ⟨44274424410267715065288179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29516282940178476710192119 44274424410267715065288179)
    ·
      refine ⟨66411636615401572597932269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44274424410267715065288179 66411636615401572597932269)
      ·
        refine ⟨24904363730775589724224601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66411636615401572597932269 24904363730775589724224601)
        ·
          refine ⟨18678272798081692293168451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24904363730775589724224601 18678272798081692293168451)
          ·
            refine ⟨28017409197122538439752677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18678272798081692293168451 28017409197122538439752677)
            ·
              refine ⟨5253264224460475957453627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28017409197122538439752677 5253264224460475957453627)
              ·
                refine ⟨7879896336690713936180441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5253264224460475957453627 7879896336690713936180441)
                ·
                  refine ⟨5909922252518035452135331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7879896336690713936180441 5909922252518035452135331)
                  ·
                    refine ⟨8864883378777053178202997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5909922252518035452135331 8864883378777053178202997)
                    ·
                      refine ⟨831082816760348735456531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8864883378777053178202997 831082816760348735456531)
                      ·
                        rfl

theorem cell23_1618528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_1618528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618528 prefixEnd_1618528 := by exact prefixLift 1618528
  have htrace : WordTrace (prefixWord ++ tailWord_1618528) baseStart_1618528 baseEnd_1618528 := by
    simpa [prefixWord, tailWord_1618528, baseEnd_1618528] using wordTrace_append hprefix tailTrace_1618528
  have hstable : (prefixWord ++ tailWord_1618528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618528).length < 2 ^ (prefixWord ++ tailWord_1618528).sum := by decide
  have hdescent : baseEnd_1618528 < baseStart_1618528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618529 : List Nat := [1, 2, 3, 1, 1, 5, 3, 1, 1, 3, 2]
def baseStart_1618529 : Nat := 118140960795 + 1618529 * 2 ^ 59
def prefixEnd_1618529 : Nat := 4983230072969 + 3 ^ 40 * 1618529 * 2
def baseEnd_1618529 : Nat := 831083330241003231544027

theorem tailTrace_1618529 : CollatzResearch.WordTrace tailWord_1618529 prefixEnd_1618529 831083330241003231544027 := by
  unfold tailWord_1618529
  simp only [CollatzResearch.WordTrace]
  refine ⟨59032602353353330591170641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39355068235568887060780427 59032602353353330591170641)
  ·
    refine ⟨44274451765014997943377981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59032602353353330591170641 44274451765014997943377981)
    ·
      refine ⟨16602919411880624228766743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44274451765014997943377981 16602919411880624228766743)
      ·
        refine ⟨24904379117820936343150115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16602919411880624228766743 24904379117820936343150115)
        ·
          refine ⟨37356568676731404514725173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24904379117820936343150115 37356568676731404514725173)
          ·
            refine ⟨3502178313443569173255485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37356568676731404514725173 3502178313443569173255485)
            ·
              refine ⟨1313316867541338439970807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3502178313443569173255485 1313316867541338439970807)
              ·
                refine ⟨1969975301312007659956211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313316867541338439970807 1969975301312007659956211)
                ·
                  refine ⟨2954962951968011489934317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1969975301312007659956211 2954962951968011489934317)
                  ·
                    refine ⟨1108111106988004308725369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2954962951968011489934317 1108111106988004308725369)
                    ·
                      refine ⟨831083330241003231544027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1108111106988004308725369 831083330241003231544027)
                      ·
                        rfl

theorem cell23_1618529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_1618529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618529 prefixEnd_1618529 := by exact prefixLift 1618529
  have htrace : WordTrace (prefixWord ++ tailWord_1618529) baseStart_1618529 baseEnd_1618529 := by
    simpa [prefixWord, tailWord_1618529, baseEnd_1618529] using wordTrace_append hprefix tailTrace_1618529
  have hstable : (prefixWord ++ tailWord_1618529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618529).length < 2 ^ (prefixWord ++ tailWord_1618529).sum := by decide
  have hdescent : baseEnd_1618529 < baseStart_1618529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618593 : List Nat := [1, 2, 3, 3, 4, 1, 1, 2, 2, 2, 2]
def baseStart_1618593 : Nat := 118140960795 + 1618593 * 2 ^ 59
def prefixEnd_1618593 : Nat := 4983230072969 + 3 ^ 40 * 1618593 * 2
def baseEnd_1618593 : Nat := 831116193002890981143733

theorem tailTrace_1618593 : CollatzResearch.WordTrace tailWord_1618593 prefixEnd_1618593 831116193002890981143733 := by
  unfold tailWord_1618593
  simp only [CollatzResearch.WordTrace]
  refine ⟨59034936625121469521500433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39356624416747646347666955 59034936625121469521500433)
  ·
    refine ⟨44276202468841102141125325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59034936625121469521500433 44276202468841102141125325)
    ·
      refine ⟨16603575925815413302921997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44276202468841102141125325 16603575925815413302921997)
      ·
        refine ⟨6226340972180779988595749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16603575925815413302921997 6226340972180779988595749)
        ·
          refine ⟨1167438932283896247861703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6226340972180779988595749 1167438932283896247861703)
          ·
            refine ⟨1751158398425844371792555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167438932283896247861703 1751158398425844371792555)
            ·
              refine ⟨2626737597638766557688833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1751158398425844371792555 2626737597638766557688833)
              ·
                refine ⟨1970053198229074918266625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2626737597638766557688833 1970053198229074918266625)
                ·
                  refine ⟨1477539898671806188699969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1970053198229074918266625 1477539898671806188699969)
                  ·
                    refine ⟨1108154924003854641524977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1477539898671806188699969 1108154924003854641524977)
                    ·
                      refine ⟨831116193002890981143733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1108154924003854641524977 831116193002890981143733)
                      ·
                        rfl

theorem cell23_1618593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_1618593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618593 prefixEnd_1618593 := by exact prefixLift 1618593
  have htrace : WordTrace (prefixWord ++ tailWord_1618593) baseStart_1618593 baseEnd_1618593 := by
    simpa [prefixWord, tailWord_1618593, baseEnd_1618593] using wordTrace_append hprefix tailTrace_1618593
  have hstable : (prefixWord ++ tailWord_1618593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618593).length < 2 ^ (prefixWord ++ tailWord_1618593).sum := by decide
  have hdescent : baseEnd_1618593 < baseStart_1618593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618659 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 3, 4]
def baseStart_1618659 : Nat := 118140960795 + 1618659 * 2 ^ 59
def prefixEnd_1618659 : Nat := 4983230072969 + 3 ^ 40 * 1618659 * 2
def baseEnd_1618659 : Nat := 277050027575362574306143

theorem tailTrace_1618659 : CollatzResearch.WordTrace tailWord_1618659 prefixEnd_1618659 277050027575362574306143 := by
  unfold tailWord_1618659
  simp only [CollatzResearch.WordTrace]
  refine ⟨59037343842882362793403031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39358229228588241862268687 59037343842882362793403031)
  ·
    refine ⟨88556015764323544190104547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59037343842882362793403031 88556015764323544190104547)
    ·
      refine ⟨132834023646485316285156821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88556015764323544190104547 132834023646485316285156821)
      ·
        refine ⟨3113297429214499600433363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 132834023646485316285156821 3113297429214499600433363)
        ·
          refine ⟨4669946143821749400650045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113297429214499600433363 4669946143821749400650045)
          ·
            refine ⟨1751229803933156025243767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4669946143821749400650045 1751229803933156025243767)
            ·
              refine ⟨2626844705899734037865651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1751229803933156025243767 2626844705899734037865651)
              ·
                refine ⟨3940267058849601056798477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2626844705899734037865651 3940267058849601056798477)
                ·
                  refine ⟨1477600147068600396299429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3940267058849601056798477 1477600147068600396299429)
                  ·
                    refine ⟨277050027575362574306143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1477600147068600396299429 277050027575362574306143)
                    ·
                      rfl

theorem cell23_1618659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 4].length) (baseStart_1618659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618659 prefixEnd_1618659 := by exact prefixLift 1618659
  have htrace : WordTrace (prefixWord ++ tailWord_1618659) baseStart_1618659 baseEnd_1618659 := by
    simpa [prefixWord, tailWord_1618659, baseEnd_1618659] using wordTrace_append hprefix tailTrace_1618659
  have hstable : (prefixWord ++ tailWord_1618659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618659).length < 2 ^ (prefixWord ++ tailWord_1618659).sum := by decide
  have hdescent : baseEnd_1618659 < baseStart_1618659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618668 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 2, 9]
def baseStart_1618668 : Nat := 118140960795 + 1618668 * 2 ^ 59
def prefixEnd_1618668 : Nat := 4983230072969 + 3 ^ 40 * 1618668 * 2
def baseEnd_1618668 : Nat := 277051568017326062568629

theorem tailTrace_1618668 : CollatzResearch.WordTrace tailWord_1618668 prefixEnd_1618668 277051568017326062568629 := by
  unfold tailWord_1618668
  simp only [CollatzResearch.WordTrace]
  refine ⟨29518836049924878665240329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39358448066566504886987105 29518836049924878665240329)
  ·
    refine ⟨22139127037443658998930247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29518836049924878665240329 22139127037443658998930247)
    ·
      refine ⟨33208690556165488498395371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22139127037443658998930247 33208690556165488498395371)
      ·
        refine ⟨49813035834248232747593057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33208690556165488498395371 49813035834248232747593057)
        ·
          refine ⟨37359776875686174560694793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49813035834248232747593057 37359776875686174560694793)
          ·
            refine ⟨28019832656764630920521095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37359776875686174560694793 28019832656764630920521095)
            ·
              refine ⟨42029748985146946380781643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28019832656764630920521095 42029748985146946380781643)
              ·
                refine ⟨63044623477720419571172465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42029748985146946380781643 63044623477720419571172465)
                ·
                  refine ⟨47283467608290314678379349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63044623477720419571172465 47283467608290314678379349)
                  ·
                    refine ⟨277051568017326062568629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 47283467608290314678379349 277051568017326062568629)
                    ·
                      rfl

theorem cell23_1618668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_1618668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618668 prefixEnd_1618668 := by exact prefixLift 1618668
  have htrace : WordTrace (prefixWord ++ tailWord_1618668) baseStart_1618668 baseEnd_1618668 := by
    simpa [prefixWord, tailWord_1618668, baseEnd_1618668] using wordTrace_append hprefix tailTrace_1618668
  have hstable : (prefixWord ++ tailWord_1618668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618668).length < 2 ^ (prefixWord ++ tailWord_1618668).sum := by decide
  have hdescent : baseEnd_1618668 < baseStart_1618668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618682 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3]
def baseStart_1618682 : Nat := 118140960795 + 1618682 * 2 ^ 59
def prefixEnd_1618682 : Nat := 4983230072969 + 3 ^ 40 * 1618682 * 2
def baseEnd_1618682 : Nat := 831161892781141132930823

theorem tailTrace_1618682 : CollatzResearch.WordTrace tailWord_1618682 prefixEnd_1618682 831161892781141132930823 := by
  unfold tailWord_1618682
  simp only [CollatzResearch.WordTrace]
  refine ⟨14759545680449759430372575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39358788481199358480993533 14759545680449759430372575)
  ·
    refine ⟨22139318520674639145558863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14759545680449759430372575 22139318520674639145558863)
    ·
      refine ⟨33208977781011958718338295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22139318520674639145558863 33208977781011958718338295)
      ·
        refine ⟨49813466671517938077507443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33208977781011958718338295 49813466671517938077507443)
        ·
          refine ⟨74720200007276907116261165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49813466671517938077507443 74720200007276907116261165)
          ·
            refine ⟨28020075002728840168597937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74720200007276907116261165 28020075002728840168597937)
            ·
              refine ⟨21015056252046630126448453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28020075002728840168597937 21015056252046630126448453)
              ·
                refine ⟨3940323047258743148709085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21015056252046630126448453 3940323047258743148709085)
                ·
                  refine ⟨1477621142722028680765907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3940323047258743148709085 1477621142722028680765907)
                  ·
                    refine ⟨2216431714083043021148861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1477621142722028680765907 2216431714083043021148861)
                    ·
                      refine ⟨831161892781141132930823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2216431714083043021148861 831161892781141132930823)
                      ·
                        rfl

theorem cell23_1618682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3].length) (baseStart_1618682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618682 prefixEnd_1618682 := by exact prefixLift 1618682
  have htrace : WordTrace (prefixWord ++ tailWord_1618682) baseStart_1618682 baseEnd_1618682 := by
    simpa [prefixWord, tailWord_1618682, baseEnd_1618682] using wordTrace_append hprefix tailTrace_1618682
  have hstable : (prefixWord ++ tailWord_1618682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618682).length < 2 ^ (prefixWord ++ tailWord_1618682).sum := by decide
  have hdescent : baseEnd_1618682 < baseStart_1618682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618685 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 3, 5]
def baseStart_1618685 : Nat := 118140960795 + 1618685 * 2 ^ 59
def prefixEnd_1618685 : Nat := 4983230072969 + 3 ^ 40 * 1618685 * 2
def baseEnd_1618685 : Nat := 277054477741034873731103

theorem tailTrace_1618685 : CollatzResearch.WordTrace tailWord_1618685 prefixEnd_1618685 277054477741034873731103 := by
  unfold tailWord_1618685
  simp only [CollatzResearch.WordTrace]
  refine ⟨59038292140788169233849509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39358861427192112822566339 59038292140788169233849509)
  ·
    refine ⟨11069679776397781731346783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59038292140788169233849509 11069679776397781731346783)
    ·
      refine ⟨16604519664596672597020175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11069679776397781731346783 16604519664596672597020175)
      ·
        refine ⟨24906779496895008895530263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16604519664596672597020175 24906779496895008895530263)
        ·
          refine ⟨37360169245342513343295395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24906779496895008895530263 37360169245342513343295395)
          ·
            refine ⟨56040253868013770014943093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37360169245342513343295395 56040253868013770014943093)
            ·
              refine ⟨5253773800126290938900915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56040253868013770014943093 5253773800126290938900915)
              ·
                refine ⟨7880660700189436408351373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5253773800126290938900915 7880660700189436408351373)
                ·
                  refine ⟨2955247762571038653131765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7880660700189436408351373 2955247762571038653131765)
                  ·
                    refine ⟨277054477741034873731103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2955247762571038653131765 277054477741034873731103)
                    ·
                      rfl

theorem cell23_1618685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_1618685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618685 prefixEnd_1618685 := by exact prefixLift 1618685
  have htrace : WordTrace (prefixWord ++ tailWord_1618685) baseStart_1618685 baseEnd_1618685 := by
    simpa [prefixWord, tailWord_1618685, baseEnd_1618685] using wordTrace_append hprefix tailTrace_1618685
  have hstable : (prefixWord ++ tailWord_1618685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618685).length < 2 ^ (prefixWord ++ tailWord_1618685).sum := by decide
  have hdescent : baseEnd_1618685 < baseStart_1618685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618699 : List Nat := [1, 1, 1, 1, 5, 1, 1, 7, 1, 1, 3]
def baseStart_1618699 : Nat := 118140960795 + 1618699 * 2 ^ 59
def prefixEnd_1618699 : Nat := 4983230072969 + 3 ^ 40 * 1618699 * 2
def baseEnd_1618699 : Nat := 831170621952267566418245

theorem tailTrace_1618699 : CollatzResearch.WordTrace tailWord_1618699 prefixEnd_1618699 831170621952267566418245 := by
  unfold tailWord_1618699
  simp only [CollatzResearch.WordTrace]
  refine ⟨59038802762737449624859151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39359201841824966416572767 59038802762737449624859151)
  ·
    refine ⟨88558204144106174437288727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59038802762737449624859151 88558204144106174437288727)
    ·
      refine ⟨132837306216159261655933091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88558204144106174437288727 132837306216159261655933091)
      ·
        refine ⟨199255959324238892483899637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132837306216159261655933091 199255959324238892483899637)
        ·
          refine ⟨18680246186647396170365591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 199255959324238892483899637 18680246186647396170365591)
          ·
            refine ⟨28020369279971094255548387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18680246186647396170365591 28020369279971094255548387)
            ·
              refine ⟨42030553919956641383322581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28020369279971094255548387 42030553919956641383322581)
              ·
                refine ⟨985091107498983782421623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42030553919956641383322581 985091107498983782421623)
                ·
                  refine ⟨1477636661248475673632435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 985091107498983782421623 1477636661248475673632435)
                  ·
                    refine ⟨2216454991872713510448653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1477636661248475673632435 2216454991872713510448653)
                    ·
                      refine ⟨831170621952267566418245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2216454991872713510448653 831170621952267566418245)
                      ·
                        rfl

theorem cell23_1618699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 1, 1, 3].length) (baseStart_1618699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618699 prefixEnd_1618699 := by exact prefixLift 1618699
  have htrace : WordTrace (prefixWord ++ tailWord_1618699) baseStart_1618699 baseEnd_1618699 := by
    simpa [prefixWord, tailWord_1618699, baseEnd_1618699] using wordTrace_append hprefix tailTrace_1618699
  have hstable : (prefixWord ++ tailWord_1618699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618699).length < 2 ^ (prefixWord ++ tailWord_1618699).sum := by decide
  have hdescent : baseEnd_1618699 < baseStart_1618699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618716 : List Nat := [2, 2, 3, 1, 1, 4, 1, 4, 1, 1, 3]
def baseStart_1618716 : Nat := 118140960795 + 1618716 * 2 ^ 59
def prefixEnd_1618716 : Nat := 4983230072969 + 3 ^ 40 * 1618716 * 2
def baseEnd_1618716 : Nat := 831179351123393999905667

theorem tailTrace_1618716 : CollatzResearch.WordTrace tailWord_1618716 prefixEnd_1618716 831179351123393999905667 := by
  unfold tailWord_1618716
  simp only [CollatzResearch.WordTrace]
  refine ⟨29519711401837930764114001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39359615202450574352152001 29519711401837930764114001)
  ·
    refine ⟨22139783551378448073085501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29519711401837930764114001 22139783551378448073085501)
    ·
      refine ⟨8302418831766918027407063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22139783551378448073085501 8302418831766918027407063)
      ·
        refine ⟨12453628247650377041110595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8302418831766918027407063 12453628247650377041110595)
        ·
          refine ⟨18680442371475565561665893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12453628247650377041110595 18680442371475565561665893)
          ·
            refine ⟨3502582944651668542812355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18680442371475565561665893 3502582944651668542812355)
            ·
              refine ⟨5253874416977502814218533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3502582944651668542812355 5253874416977502814218533)
              ·
                refine ⟨985101453183281777665975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5253874416977502814218533 985101453183281777665975)
                ·
                  refine ⟨1477652179774922666498963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 985101453183281777665975 1477652179774922666498963)
                  ·
                    refine ⟨2216478269662383999748445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1477652179774922666498963 2216478269662383999748445)
                    ·
                      refine ⟨831179351123393999905667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2216478269662383999748445 831179351123393999905667)
                      ·
                        rfl

theorem cell23_1618716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_1618716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618716 prefixEnd_1618716 := by exact prefixLift 1618716
  have htrace : WordTrace (prefixWord ++ tailWord_1618716) baseStart_1618716 baseEnd_1618716 := by
    simpa [prefixWord, tailWord_1618716, baseEnd_1618716] using wordTrace_append hprefix tailTrace_1618716
  have hstable : (prefixWord ++ tailWord_1618716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618716).length < 2 ^ (prefixWord ++ tailWord_1618716).sum := by decide
  have hdescent : baseEnd_1618716 < baseStart_1618716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618722 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_1618722 : Nat := 118140960795 + 1618722 * 2 ^ 59
def prefixEnd_1618722 : Nat := 4983230072969 + 3 ^ 40 * 1618722 * 2
def baseEnd_1618722 : Nat := 831182432007320976430639

theorem tailTrace_1618722 : CollatzResearch.WordTrace tailWord_1618722 prefixEnd_1618722 831182432007320976430639 := by
  unfold tailWord_1618722
  simp only [CollatzResearch.WordTrace]
  refine ⟨14759910410413531138236605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39359761094436083035297613 14759910410413531138236605)
  ·
    refine ⟨5534966403905074176838727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14759910410413531138236605 5534966403905074176838727)
    ·
      refine ⟨8302449605857611265258091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5534966403905074176838727 8302449605857611265258091)
      ·
        refine ⟨12453674408786416897887137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8302449605857611265258091 12453674408786416897887137)
        ·
          refine ⟨9340255806589812673415353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12453674408786416897887137 9340255806589812673415353)
          ·
            refine ⟨7005191854942359505061515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9340255806589812673415353 7005191854942359505061515)
            ·
              refine ⟨10507787782413539257592273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7005191854942359505061515 10507787782413539257592273)
              ·
                refine ⟨7880840836810154443194205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10507787782413539257592273 7880840836810154443194205)
                ·
                  refine ⟨2955315313803807916197827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7880840836810154443194205 2955315313803807916197827)
                  ·
                    refine ⟨4432972970705711874296741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2955315313803807916197827 4432972970705711874296741)
                    ·
                      refine ⟨831182432007320976430639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4432972970705711874296741 831182432007320976430639)
                      ·
                        rfl

theorem cell23_1618722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_1618722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618722 prefixEnd_1618722 := by exact prefixLift 1618722
  have htrace : WordTrace (prefixWord ++ tailWord_1618722) baseStart_1618722 baseEnd_1618722 := by
    simpa [prefixWord, tailWord_1618722, baseEnd_1618722] using wordTrace_append hprefix tailTrace_1618722
  have hstable : (prefixWord ++ tailWord_1618722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618722).length < 2 ^ (prefixWord ++ tailWord_1618722).sum := by decide
  have hdescent : baseEnd_1618722 < baseStart_1618722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618725 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 3, 1, 5]
def baseStart_1618725 : Nat := 118140960795 + 1618725 * 2 ^ 59
def prefixEnd_1618725 : Nat := 4983230072969 + 3 ^ 40 * 1618725 * 2
def baseEnd_1618725 : Nat := 831183972449284464693125

theorem tailTrace_1618725 : CollatzResearch.WordTrace tailWord_1618725 prefixEnd_1618725 831183972449284464693125 := by
  unfold tailWord_1618725
  simp only [CollatzResearch.WordTrace]
  refine ⟨59039751060643256065305629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39359834040428837376870419 59039751060643256065305629)
  ·
    refine ⟨22139906647741221024489611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59039751060643256065305629 22139906647741221024489611)
    ·
      refine ⟨33209859971611831536734417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22139906647741221024489611 33209859971611831536734417)
      ·
        refine ⟨24907394978708873652550813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33209859971611831536734417 24907394978708873652550813)
        ·
          refine ⟨9340273117015827619706555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24907394978708873652550813 9340273117015827619706555)
          ·
            refine ⟨14010409675523741429559833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9340273117015827619706555 14010409675523741429559833)
            ·
              refine ⟨10507807256642806072169875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14010409675523741429559833 10507807256642806072169875)
              ·
                refine ⟨15761710884964209108254813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10507807256642806072169875 15761710884964209108254813)
                ·
                  refine ⟨5910641581861578415595555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15761710884964209108254813 5910641581861578415595555)
                  ·
                    refine ⟨8865962372792367623393333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5910641581861578415595555 8865962372792367623393333)
                    ·
                      refine ⟨831183972449284464693125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8865962372792367623393333 831183972449284464693125)
                      ·
                        rfl

theorem cell23_1618725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_1618725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618725 prefixEnd_1618725 := by exact prefixLift 1618725
  have htrace : WordTrace (prefixWord ++ tailWord_1618725) baseStart_1618725 baseEnd_1618725 := by
    simpa [prefixWord, tailWord_1618725, baseEnd_1618725] using wordTrace_append hprefix tailTrace_1618725
  have hstable : (prefixWord ++ tailWord_1618725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618725).length < 2 ^ (prefixWord ++ tailWord_1618725).sum := by decide
  have hdescent : baseEnd_1618725 < baseStart_1618725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618732 : List Nat := [2, 2, 1, 1, 1, 4, 1, 5, 2, 4]
def baseStart_1618732 : Nat := 118140960795 + 1618732 * 2 ^ 59
def prefixEnd_1618732 : Nat := 4983230072969 + 3 ^ 40 * 1618732 * 2
def baseEnd_1618732 : Nat := 277062522271288645768531

theorem tailTrace_1618732 : CollatzResearch.WordTrace tailWord_1618732 prefixEnd_1618732 277062522271288645768531 := by
  unfold tailWord_1618732
  simp only [CollatzResearch.WordTrace]
  refine ⟨29520003185808948130405225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39360004247745264173873633 29520003185808948130405225)
  ·
    refine ⟨22140002389356711097803919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29520003185808948130405225 22140002389356711097803919)
    ·
      refine ⟨33210003584035066646705879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22140002389356711097803919 33210003584035066646705879)
      ·
        refine ⟨49815005376052599970058819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33210003584035066646705879 49815005376052599970058819)
        ·
          refine ⟨74722508064078899955088229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49815005376052599970058819 74722508064078899955088229)
          ·
            refine ⟨14010470262014793741579043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74722508064078899955088229 14010470262014793741579043)
            ·
              refine ⟨21015705393022190612368565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14010470262014793741579043 21015705393022190612368565)
              ·
                refine ⟨1970222380595830369909553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21015705393022190612368565 1970222380595830369909553)
                ·
                  refine ⟨1477666785446872777432165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1970222380595830369909553 1477666785446872777432165)
                  ·
                    refine ⟨277062522271288645768531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1477666785446872777432165 277062522271288645768531)
                    ·
                      rfl

theorem cell23_1618732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_1618732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618732 prefixEnd_1618732 := by exact prefixLift 1618732
  have htrace : WordTrace (prefixWord ++ tailWord_1618732) baseStart_1618732 baseEnd_1618732 := by
    simpa [prefixWord, tailWord_1618732, baseEnd_1618732] using wordTrace_append hprefix tailTrace_1618732
  have hstable : (prefixWord ++ tailWord_1618732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618732).length < 2 ^ (prefixWord ++ tailWord_1618732).sum := by decide
  have hdescent : baseEnd_1618732 < baseStart_1618732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618733 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1618733 : Nat := 118140960795 + 1618733 * 2 ^ 59
def prefixEnd_1618733 : Nat := 4983230072969 + 3 ^ 40 * 1618733 * 2
def baseEnd_1618733 : Nat := 831188080294520433393089

theorem tailTrace_1618733 : CollatzResearch.WordTrace tailWord_1618733 prefixEnd_1618733 831188080294520433393089 := by
  unfold tailWord_1618733
  simp only [CollatzResearch.WordTrace]
  refine ⟨59040042844614273431596853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39360028563076182287731235 59040042844614273431596853)
  ·
    refine ⟨5535004016682588134212205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59040042844614273431596853 5535004016682588134212205)
    ·
      refine ⟨2075626506255970550329577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5535004016682588134212205 2075626506255970550329577)
      ·
        refine ⟨1556719879691977912747183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2075626506255970550329577 1556719879691977912747183)
        ·
          refine ⟨2335079819537966869120775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1556719879691977912747183 2335079819537966869120775)
          ·
            refine ⟨3502619729306950303681163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2335079819537966869120775 3502619729306950303681163)
            ·
              refine ⟨5253929593960425455521745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3502619729306950303681163 5253929593960425455521745)
              ·
                refine ⟨3940447195470319091641309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5253929593960425455521745 3940447195470319091641309)
                ·
                  refine ⟨1477667698301369659365491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3940447195470319091641309 1477667698301369659365491)
                  ·
                    refine ⟨2216501547452054489048237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1477667698301369659365491 2216501547452054489048237)
                    ·
                      refine ⟨831188080294520433393089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2216501547452054489048237 831188080294520433393089)
                      ·
                        rfl

theorem cell23_1618733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1618733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618733 prefixEnd_1618733 := by exact prefixLift 1618733
  have htrace : WordTrace (prefixWord ++ tailWord_1618733) baseStart_1618733 baseEnd_1618733 := by
    simpa [prefixWord, tailWord_1618733, baseEnd_1618733] using wordTrace_append hprefix tailTrace_1618733
  have hstable : (prefixWord ++ tailWord_1618733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618733).length < 2 ^ (prefixWord ++ tailWord_1618733).sum := by decide
  have hdescent : baseEnd_1618733 < baseStart_1618733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618739 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 5, 2, 2]
def baseStart_1618739 : Nat := 118140960795 + 1618739 * 2 ^ 59
def prefixEnd_1618739 : Nat := 4983230072969 + 3 ^ 40 * 1618739 * 2
def baseEnd_1618739 : Nat := 831191161178447409918061

theorem tailTrace_1618739 : CollatzResearch.WordTrace tailWord_1618739 prefixEnd_1618739 831191161178447409918061 := by
  unfold tailWord_1618739
  simp only [CollatzResearch.WordTrace]
  refine ⟨59040261682592536456315271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39360174455061690970876847 59040261682592536456315271)
  ·
    refine ⟨88560392523888804684472907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59040261682592536456315271 88560392523888804684472907)
    ·
      refine ⟨132840588785833207026709361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88560392523888804684472907 132840588785833207026709361)
      ·
        refine ⟨99630441589374905270032021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132840588785833207026709361 99630441589374905270032021)
        ·
          refine ⟨4670176949501948684532751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 99630441589374905270032021 4670176949501948684532751)
          ·
            refine ⟨7005265424252923026799127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4670176949501948684532751 7005265424252923026799127)
            ·
              refine ⟨10507898136379384540198691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7005265424252923026799127 10507898136379384540198691)
              ·
                refine ⟨15761847204569076810298037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10507898136379384540198691 15761847204569076810298037)
                ·
                  refine ⟨1477673175428350950965441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15761847204569076810298037 1477673175428350950965441)
                  ·
                    refine ⟨1108254881571263213224081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1477673175428350950965441 1108254881571263213224081)
                    ·
                      refine ⟨831191161178447409918061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1108254881571263213224081 831191161178447409918061)
                      ·
                        rfl

theorem cell23_1618739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 2, 2].length) (baseStart_1618739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618739 prefixEnd_1618739 := by exact prefixLift 1618739
  have htrace : WordTrace (prefixWord ++ tailWord_1618739) baseStart_1618739 baseEnd_1618739 := by
    simpa [prefixWord, tailWord_1618739, baseEnd_1618739] using wordTrace_append hprefix tailTrace_1618739
  have hstable : (prefixWord ++ tailWord_1618739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618739).length < 2 ^ (prefixWord ++ tailWord_1618739).sum := by decide
  have hdescent : baseEnd_1618739 < baseStart_1618739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618753 : List Nat := [1, 2, 5, 3, 1, 2, 2, 1, 1, 5]
def baseStart_1618753 : Nat := 118140960795 + 1618753 * 2 ^ 59
def prefixEnd_1618753 : Nat := 4983230072969 + 3 ^ 40 * 1618753 * 2
def baseEnd_1618753 : Nat := 277066116635870118380999

theorem tailTrace_1618753 : CollatzResearch.WordTrace tailWord_1618753 prefixEnd_1618753 277066116635870118380999 := by
  unfold tailWord_1618753
  simp only [CollatzResearch.WordTrace]
  refine ⟨59040772304541816847324913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39360514869694544564883275 59040772304541816847324913)
  ·
    refine ⟨44280579228406362635493685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59040772304541816847324913 44280579228406362635493685)
    ·
      refine ⟨4151304302663096497077533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44280579228406362635493685 4151304302663096497077533)
      ·
        refine ⟨1556739113498661186404075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4151304302663096497077533 1556739113498661186404075)
        ·
          refine ⟨2335108670247991779606113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1556739113498661186404075 2335108670247991779606113)
          ·
            refine ⟨1751331502685993834704585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2335108670247991779606113 1751331502685993834704585)
            ·
              refine ⟨1313498627014495376028439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1751331502685993834704585 1313498627014495376028439)
              ·
                refine ⟨1970247940521743064042659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313498627014495376028439 1970247940521743064042659)
                ·
                  refine ⟨2955371910782614596063989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1970247940521743064042659 2955371910782614596063989)
                  ·
                    refine ⟨277066116635870118380999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2955371910782614596063989 277066116635870118380999)
                    ·
                      rfl

theorem cell23_1618753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_1618753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618753 prefixEnd_1618753 := by exact prefixLift 1618753
  have htrace : WordTrace (prefixWord ++ tailWord_1618753) baseStart_1618753 baseEnd_1618753 := by
    simpa [prefixWord, tailWord_1618753, baseEnd_1618753] using wordTrace_append hprefix tailTrace_1618753
  have hstable : (prefixWord ++ tailWord_1618753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618753).length < 2 ^ (prefixWord ++ tailWord_1618753).sum := by decide
  have hdescent : baseEnd_1618753 < baseStart_1618753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618786 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_1618786 : Nat := 118140960795 + 1618786 * 2 ^ 59
def prefixEnd_1618786 : Nat := 4983230072969 + 3 ^ 40 * 1618786 * 2
def baseEnd_1618786 : Nat := 831215294769208726030345

theorem tailTrace_1618786 : CollatzResearch.WordTrace tailWord_1618786 prefixEnd_1618786 831215294769208726030345 := by
  unfold tailWord_1618786
  simp only [CollatzResearch.WordTrace]
  refine ⟨14760493978355565870819053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39361317275614842322184141 14760493978355565870819053)
  ·
    refine ⟨5535185241883337201557145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14760493978355565870819053 5535185241883337201557145)
    ·
      refine ⟨4151388931412502901167859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5535185241883337201557145 4151388931412502901167859)
      ·
        refine ⟨6227083397118754351751789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4151388931412502901167859 6227083397118754351751789)
        ·
          refine ⟨2335156273919532881906921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6227083397118754351751789 2335156273919532881906921)
          ·
            refine ⟨1751367205439649661430191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2335156273919532881906921 1751367205439649661430191)
            ·
              refine ⟨2627050808159474492145287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1751367205439649661430191 2627050808159474492145287)
              ·
                refine ⟨3940576212239211738217931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2627050808159474492145287 3940576212239211738217931)
                ·
                  refine ⟨5910864318358817607326897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3940576212239211738217931 5910864318358817607326897)
                  ·
                    refine ⟨4433148238769113205495173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5910864318358817607326897 4433148238769113205495173)
                    ·
                      refine ⟨831215294769208726030345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4433148238769113205495173 831215294769208726030345)
                      ·
                        rfl

theorem cell23_1618786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_1618786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618786 prefixEnd_1618786 := by exact prefixLift 1618786
  have htrace : WordTrace (prefixWord ++ tailWord_1618786) baseStart_1618786 baseEnd_1618786 := by
    simpa [prefixWord, tailWord_1618786, baseEnd_1618786] using wordTrace_append hprefix tailTrace_1618786
  have hstable : (prefixWord ++ tailWord_1618786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618786).length < 2 ^ (prefixWord ++ tailWord_1618786).sum := by decide
  have hdescent : baseEnd_1618786 < baseStart_1618786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618789 : List Nat := [1, 3, 1, 3, 1, 1, 2, 5, 2, 1, 3]
def baseStart_1618789 : Nat := 118140960795 + 1618789 * 2 ^ 59
def prefixEnd_1618789 : Nat := 4983230072969 + 3 ^ 40 * 1618789 * 2
def baseEnd_1618789 : Nat := 831216835211172214292831

theorem tailTrace_1618789 : CollatzResearch.WordTrace tailWord_1618789 prefixEnd_1618789 831216835211172214292831 := by
  unfold tailWord_1618789
  simp only [CollatzResearch.WordTrace]
  refine ⟨59042085332411394995635421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39361390221607596663756947 59042085332411394995635421)
  ·
    refine ⟨22140781999654273123363283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59042085332411394995635421 22140781999654273123363283)
    ·
      refine ⟨33211172999481409685044925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22140781999654273123363283 33211172999481409685044925)
      ·
        refine ⟨12454189874805528631891847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33211172999481409685044925 12454189874805528631891847)
        ·
          refine ⟨18681284812208292947837771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12454189874805528631891847 18681284812208292947837771)
          ·
            refine ⟨28021927218312439421756657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18681284812208292947837771 28021927218312439421756657)
            ·
              refine ⟨21016445413734329566317493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28021927218312439421756657 21016445413734329566317493)
              ·
                refine ⟨1970291757537593396842265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21016445413734329566317493 1970291757537593396842265)
                ·
                  refine ⟨1477718818153195047631699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1970291757537593396842265 1477718818153195047631699)
                  ·
                    refine ⟨2216578227229792571447549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1477718818153195047631699 2216578227229792571447549)
                    ·
                      refine ⟨831216835211172214292831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2216578227229792571447549 831216835211172214292831)
                      ·
                        rfl

theorem cell23_1618789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_1618789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618789 prefixEnd_1618789 := by exact prefixLift 1618789
  have htrace : WordTrace (prefixWord ++ tailWord_1618789) baseStart_1618789 baseEnd_1618789 := by
    simpa [prefixWord, tailWord_1618789, baseEnd_1618789] using wordTrace_append hprefix tailTrace_1618789
  have hstable : (prefixWord ++ tailWord_1618789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618789).length < 2 ^ (prefixWord ++ tailWord_1618789).sum := by decide
  have hdescent : baseEnd_1618789 < baseStart_1618789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618795 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 4]
def baseStart_1618795 : Nat := 118140960795 + 1618795 * 2 ^ 59
def prefixEnd_1618795 : Nat := 4983230072969 + 3 ^ 40 * 1618795 * 2
def baseEnd_1618795 : Nat := 831219916095099190817803

theorem tailTrace_1618795 : CollatzResearch.WordTrace tailWord_1618795 prefixEnd_1618795 831219916095099190817803 := by
  unfold tailWord_1618795
  simp only [CollatzResearch.WordTrace]
  refine ⟨59042304170389658020353839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39361536113593105346902559 59042304170389658020353839)
  ·
    refine ⟨88563456255584487030530759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59042304170389658020353839 88563456255584487030530759)
    ·
      refine ⟨132845184383376730545796139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88563456255584487030530759 132845184383376730545796139)
      ·
        refine ⟨199267776575065095818694209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132845184383376730545796139 199267776575065095818694209)
        ·
          refine ⟨149450832431298821864020657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199267776575065095818694209 149450832431298821864020657)
          ·
            refine ⟨112088124323474116398015493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149450832431298821864020657 112088124323474116398015493)
            ·
              refine ⟨21016523310651396824627905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112088124323474116398015493 21016523310651396824627905)
              ·
                refine ⟨15762392482988547618470929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21016523310651396824627905 15762392482988547618470929)
                ·
                  refine ⟨11821794362241410713853197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15762392482988547618470929 11821794362241410713853197)
                  ·
                    refine ⟨4433172885840529017694949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11821794362241410713853197 4433172885840529017694949)
                    ·
                      refine ⟨831219916095099190817803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4433172885840529017694949 831219916095099190817803)
                      ·
                        rfl

theorem cell23_1618795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 4].length) (baseStart_1618795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618795 prefixEnd_1618795 := by exact prefixLift 1618795
  have htrace : WordTrace (prefixWord ++ tailWord_1618795) baseStart_1618795 baseEnd_1618795 := by
    simpa [prefixWord, tailWord_1618795, baseEnd_1618795] using wordTrace_append hprefix tailTrace_1618795
  have hstable : (prefixWord ++ tailWord_1618795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618795).length < 2 ^ (prefixWord ++ tailWord_1618795).sum := by decide
  have hdescent : baseEnd_1618795 < baseStart_1618795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618806 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1618806 : Nat := 118140960795 + 1618806 * 2 ^ 59
def prefixEnd_1618806 : Nat := 4983230072969 + 3 ^ 40 * 1618806 * 2
def baseEnd_1618806 : Nat := 831225564382298647780253

theorem tailTrace_1618806 : CollatzResearch.WordTrace tailWord_1618806 prefixEnd_1618806 831225564382298647780253 := by
  unfold tailWord_1618806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3690169085834362931187767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39361803582233204599336181 3690169085834362931187767)
  ·
    refine ⟨5535253628751544396781651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3690169085834362931187767 5535253628751544396781651)
    ·
      refine ⟨8302880443127316595172477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5535253628751544396781651 8302880443127316595172477)
      ·
        refine ⟨3113580166172743723189679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8302880443127316595172477 3113580166172743723189679)
        ·
          refine ⟨4670370249259115584784519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113580166172743723189679 4670370249259115584784519)
          ·
            refine ⟨7005555373888673377176779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4670370249259115584784519 7005555373888673377176779)
            ·
              refine ⟨10508333060833010065765169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7005555373888673377176779 10508333060833010065765169)
              ·
                refine ⟨7881249795624757549323877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10508333060833010065765169 7881249795624757549323877)
                ·
                  refine ⟨1477734336679642040498227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7881249795624757549323877 1477734336679642040498227)
                  ·
                    refine ⟨2216601505019463060747341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1477734336679642040498227 2216601505019463060747341)
                    ·
                      refine ⟨831225564382298647780253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2216601505019463060747341 831225564382298647780253)
                      ·
                        rfl

theorem cell23_1618806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1618806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618806 prefixEnd_1618806 := by exact prefixLift 1618806
  have htrace : WordTrace (prefixWord ++ tailWord_1618806) baseStart_1618806 baseEnd_1618806 := by
    simpa [prefixWord, tailWord_1618806, baseEnd_1618806] using wordTrace_append hprefix tailTrace_1618806
  have hstable : (prefixWord ++ tailWord_1618806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618806).length < 2 ^ (prefixWord ++ tailWord_1618806).sum := by decide
  have hdescent : baseEnd_1618806 < baseStart_1618806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618815 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 5]
def baseStart_1618815 : Nat := 118140960795 + 1618815 * 2 ^ 59
def prefixEnd_1618815 : Nat := 4983230072969 + 3 ^ 40 * 1618815 * 2
def baseEnd_1618815 : Nat := 831230185708189112567711

theorem tailTrace_1618815 : CollatzResearch.WordTrace tailWord_1618815 prefixEnd_1618815 831230185708189112567711 := by
  unfold tailWord_1618815
  simp only [CollatzResearch.WordTrace]
  refine ⟨59043033630317201436081899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39362022420211467624054599 59043033630317201436081899)
  ·
    refine ⟨88564550445475802154122849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59043033630317201436081899 88564550445475802154122849)
    ·
      refine ⟨66423412834106851615592137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88564550445475802154122849 66423412834106851615592137)
      ·
        refine ⟨49817559625580138711694103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66423412834106851615592137 49817559625580138711694103)
        ·
          refine ⟨74726339438370208067541155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49817559625580138711694103 74726339438370208067541155)
          ·
            refine ⟨112089509157555312101311733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74726339438370208067541155 112089509157555312101311733)
            ·
              refine ⟨10508391483520810509497975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112089509157555312101311733 10508391483520810509497975)
              ·
                refine ⟨15762587225281215764246963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10508391483520810509497975 15762587225281215764246963)
                ·
                  refine ⟨23643880837921823646370445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15762587225281215764246963 23643880837921823646370445)
                  ·
                    refine ⟨8866455314220683867388917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23643880837921823646370445 8866455314220683867388917)
                    ·
                      refine ⟨831230185708189112567711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8866455314220683867388917 831230185708189112567711)
                      ·
                        rfl

theorem cell23_1618815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_1618815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618815 prefixEnd_1618815 := by exact prefixLift 1618815
  have htrace : WordTrace (prefixWord ++ tailWord_1618815) baseStart_1618815 baseEnd_1618815 := by
    simpa [prefixWord, tailWord_1618815, baseEnd_1618815] using wordTrace_append hprefix tailTrace_1618815
  have hstable : (prefixWord ++ tailWord_1618815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618815).length < 2 ^ (prefixWord ++ tailWord_1618815).sum := by decide
  have hdescent : baseEnd_1618815 < baseStart_1618815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618835 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 7]
def baseStart_1618835 : Nat := 118140960795 + 1618835 * 2 ^ 59
def prefixEnd_1618835 : Nat := 4983230072969 + 3 ^ 40 * 1618835 * 2
def baseEnd_1618835 : Nat := 92360050591253226035291

theorem tailTrace_1618835 : CollatzResearch.WordTrace tailWord_1618835 prefixEnd_1618835 92360050591253226035291 := by
  unfold tailWord_1618835
  simp only [CollatzResearch.WordTrace]
  refine ⟨59043763090244744851809959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39362508726829829901206639 59043763090244744851809959)
  ·
    refine ⟨88565644635367117277714939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59043763090244744851809959 88565644635367117277714939)
    ·
      refine ⟨132848466953050675916572409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88565644635367117277714939 132848466953050675916572409)
      ·
        refine ⟨99636350214788006937429307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132848466953050675916572409 99636350214788006937429307)
        ·
          refine ⟨149454525322182010406143961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99636350214788006937429307 149454525322182010406143961)
          ·
            refine ⟨112090893991636507804607971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149454525322182010406143961 112090893991636507804607971)
            ·
              refine ⟨168136340987454761706911957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112090893991636507804607971 168136340987454761706911957)
              ·
                refine ⟨3940695491893470977505749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 168136340987454761706911957 3940695491893470977505749)
                ·
                  refine ⟨92360050591253226035291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3940695491893470977505749 92360050591253226035291)
                  ·
                    rfl

theorem cell23_1618835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 7].length) (baseStart_1618835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618835 prefixEnd_1618835 := by exact prefixLift 1618835
  have htrace : WordTrace (prefixWord ++ tailWord_1618835) baseStart_1618835 baseEnd_1618835 := by
    simpa [prefixWord, tailWord_1618835, baseEnd_1618835] using wordTrace_append hprefix tailTrace_1618835
  have hstable : (prefixWord ++ tailWord_1618835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618835).length < 2 ^ (prefixWord ++ tailWord_1618835).sum := by decide
  have hdescent : baseEnd_1618835 < baseStart_1618835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618869 : List Nat := [1, 3, 3, 2, 1, 1, 2, 5, 5]
def baseStart_1618869 : Nat := 118140960795 + 1618869 * 2 ^ 59
def prefixEnd_1618869 : Nat := 4983230072969 + 3 ^ 40 * 1618869 * 2
def baseEnd_1618869 : Nat := 92361990407059100143607

theorem tailTrace_1618869 : CollatzResearch.WordTrace tailWord_1618869 prefixEnd_1618869 92361990407059100143607 := by
  unfold tailWord_1618869
  simp only [CollatzResearch.WordTrace]
  refine ⟨59045003172121568658547661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39363335448081045772365107 59045003172121568658547661)
  ·
    refine ⟨22141876189545588246955373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59045003172121568658547661 22141876189545588246955373)
    ·
      refine ⟨8303203571079595592608265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22141876189545588246955373 8303203571079595592608265)
      ·
        refine ⟨6227402678309696694456199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8303203571079595592608265 6227402678309696694456199)
        ·
          refine ⟨9341104017464545041684299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6227402678309696694456199 9341104017464545041684299)
          ·
            refine ⟨14011656026196817562526449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9341104017464545041684299 14011656026196817562526449)
            ·
              refine ⟨10508742019647613171894837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14011656026196817562526449 10508742019647613171894837)
              ·
                refine ⟨985194564341963734865141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10508742019647613171894837 985194564341963734865141)
                ·
                  refine ⟨92361990407059100143607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 985194564341963734865141 92361990407059100143607)
                  ·
                    rfl

theorem cell23_1618869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 5].length) (baseStart_1618869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618869 prefixEnd_1618869 := by exact prefixLift 1618869
  have htrace : WordTrace (prefixWord ++ tailWord_1618869) baseStart_1618869 baseEnd_1618869 := by
    simpa [prefixWord, tailWord_1618869, baseEnd_1618869] using wordTrace_append hprefix tailTrace_1618869
  have hstable : (prefixWord ++ tailWord_1618869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618869).length < 2 ^ (prefixWord ++ tailWord_1618869).sum := by decide
  have hdescent : baseEnd_1618869 < baseStart_1618869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618892 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1618892 : Nat := 118140960795 + 1618892 * 2 ^ 59
def prefixEnd_1618892 : Nat := 4983230072969 + 3 ^ 40 * 1618892 * 2
def baseEnd_1618892 : Nat := 831269723718585311304857

theorem tailTrace_1618892 : CollatzResearch.WordTrace tailWord_1618892 prefixEnd_1618892 831269723718585311304857 := by
  unfold tailWord_1618892
  simp only [CollatzResearch.WordTrace]
  refine ⟨29522921025519121793317465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39363894700692162391089953 29522921025519121793317465)
  ·
    refine ⟨22142190769139341344988099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29522921025519121793317465 22142190769139341344988099)
    ·
      refine ⟨33213286153709012017482149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22142190769139341344988099 33213286153709012017482149)
      ·
        refine ⟨6227491153820439753277903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33213286153709012017482149 6227491153820439753277903)
        ·
          refine ⟨9341236730730659629916855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6227491153820439753277903 9341236730730659629916855)
          ·
            refine ⟨14011855096095989444875283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9341236730730659629916855 14011855096095989444875283)
            ·
              refine ⟨21017782644143984167312925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14011855096095989444875283 21017782644143984167312925)
              ·
                refine ⟨7881668491553994062742347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21017782644143984167312925 7881668491553994062742347)
                ·
                  refine ⟨11822502737330991094113521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7881668491553994062742347 11822502737330991094113521)
                  ·
                    refine ⟨8866877052998243320585141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11822502737330991094113521 8866877052998243320585141)
                    ·
                      refine ⟨831269723718585311304857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8866877052998243320585141 831269723718585311304857)
                      ·
                        rfl

theorem cell23_1618892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1618892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618892 prefixEnd_1618892 := by exact prefixLift 1618892
  have htrace : WordTrace (prefixWord ++ tailWord_1618892) baseStart_1618892 baseEnd_1618892 := by
    simpa [prefixWord, tailWord_1618892, baseEnd_1618892] using wordTrace_append hprefix tailTrace_1618892
  have hstable : (prefixWord ++ tailWord_1618892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618892).length < 2 ^ (prefixWord ++ tailWord_1618892).sum := by decide
  have hdescent : baseEnd_1618892 < baseStart_1618892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618919 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1618919 : Nat := 118140960795 + 1618919 * 2 ^ 59
def prefixEnd_1618919 : Nat := 4983230072969 + 3 ^ 40 * 1618919 * 2
def baseEnd_1618919 : Nat := 831283587696256705667233

theorem tailTrace_1618919 : CollatzResearch.WordTrace tailWord_1618919 prefixEnd_1618919 831283587696256705667233 := by
  unfold tailWord_1618919
  simp only [CollatzResearch.WordTrace]
  refine ⟨59046826821940427197867811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39364551214626951465245207 59046826821940427197867811)
  ·
    refine ⟨88570240232910640796801717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59046826821940427197867811 88570240232910640796801717)
    ·
      refine ⟨8303460021835372574700161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88570240232910640796801717 8303460021835372574700161)
      ·
        refine ⟨6227595016376529431025121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8303460021835372574700161 6227595016376529431025121)
        ·
          refine ⟨4670696262282397073268841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6227595016376529431025121 4670696262282397073268841)
          ·
            refine ⟨3503022196711797804951631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4670696262282397073268841 3503022196711797804951631)
            ·
              refine ⟨5254533295067696707427447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3503022196711797804951631 5254533295067696707427447)
              ·
                refine ⟨7881799942601545061141171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5254533295067696707427447 7881799942601545061141171)
                ·
                  refine ⟨11822699913902317591711757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7881799942601545061141171 11822699913902317591711757)
                  ·
                    refine ⟨4433512467713369096891909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11822699913902317591711757 4433512467713369096891909)
                    ·
                      refine ⟨831283587696256705667233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4433512467713369096891909 831283587696256705667233)
                      ·
                        rfl

theorem cell23_1618919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1618919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618919 prefixEnd_1618919 := by exact prefixLift 1618919
  have htrace : WordTrace (prefixWord ++ tailWord_1618919) baseStart_1618919 baseEnd_1618919 := by
    simpa [prefixWord, tailWord_1618919, baseEnd_1618919] using wordTrace_append hprefix tailTrace_1618919
  have hstable : (prefixWord ++ tailWord_1618919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618919).length < 2 ^ (prefixWord ++ tailWord_1618919).sum := by decide
  have hdescent : baseEnd_1618919 < baseStart_1618919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618980 : List Nat := [2, 3, 1, 4, 1, 3, 1, 3, 1, 4]
def baseStart_1618980 : Nat := 118140960795 + 1618980 * 2 ^ 59
def prefixEnd_1618980 : Nat := 4983230072969 + 3 ^ 40 * 1618980 * 2
def baseEnd_1618980 : Nat := 277104970005393655668151

theorem tailTrace_1618980 : CollatzResearch.WordTrace tailWord_1618980 prefixEnd_1618980 277104970005393655668151 := by
  unfold tailWord_1618980
  simp only [CollatzResearch.WordTrace]
  refine ⟨29524525837359717307919197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39366034449812956410558929 29524525837359717307919197)
  ·
    refine ⟨11071697189009893990469699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29524525837359717307919197 11071697189009893990469699)
    ·
      refine ⟨16607545783514840985704549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11071697189009893990469699 16607545783514840985704549)
      ·
        refine ⟨3113914834409032684819603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16607545783514840985704549 3113914834409032684819603)
        ·
          refine ⟨4670872251613549027229405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113914834409032684819603 4670872251613549027229405)
          ·
            refine ⟨1751577094355080885211027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4670872251613549027229405 1751577094355080885211027)
            ·
              refine ⟨2627365641532621327816541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1751577094355080885211027 2627365641532621327816541)
              ·
                refine ⟨985262115574732997931203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2627365641532621327816541 985262115574732997931203)
                ·
                  refine ⟨1477893173362099496896805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 985262115574732997931203 1477893173362099496896805)
                  ·
                    refine ⟨277104970005393655668151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1477893173362099496896805 277104970005393655668151)
                    ·
                      rfl

theorem cell23_1618980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_1618980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1618980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1618980 prefixEnd_1618980 := by exact prefixLift 1618980
  have htrace : WordTrace (prefixWord ++ tailWord_1618980) baseStart_1618980 baseEnd_1618980 := by
    simpa [prefixWord, tailWord_1618980, baseEnd_1618980] using wordTrace_append hprefix tailTrace_1618980
  have hstable : (prefixWord ++ tailWord_1618980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618980).length < 2 ^ (prefixWord ++ tailWord_1618980).sum := by decide
  have hdescent : baseEnd_1618980 < baseStart_1618980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619026 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_1619026 : Nat := 118140960795 + 1619026 * 2 ^ 59
def prefixEnd_1619026 : Nat := 4983230072969 + 3 ^ 40 * 1619026 * 2
def baseEnd_1619026 : Nat := 831338530126287787029241

theorem tailTrace_1619026 : CollatzResearch.WordTrace tailWord_1619026 prefixEnd_1619026 831338530126287787029241 := by
  unfold tailWord_1619026
  simp only [CollatzResearch.WordTrace]
  refine ⟨14762682358138196118003233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39367152955035189648008621 14762682358138196118003233)
  ·
    refine ⟨11072011768603647088502425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14762682358138196118003233 11072011768603647088502425)
    ·
      refine ⟨8304008826452735316376819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11072011768603647088502425 8304008826452735316376819)
      ·
        refine ⟨12456013239679102974565229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8304008826452735316376819 12456013239679102974565229)
        ·
          refine ⟨4671004964879663615461961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12456013239679102974565229 4671004964879663615461961)
          ·
            refine ⟨3503253723659747711596471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4671004964879663615461961 3503253723659747711596471)
            ·
              refine ⟨5254880585489621567394707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3503253723659747711596471 5254880585489621567394707)
              ·
                refine ⟨7882320878234432351092061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5254880585489621567394707 7882320878234432351092061)
                ·
                  refine ⟨2955870329337912131659523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7882320878234432351092061 2955870329337912131659523)
                  ·
                    refine ⟨4433805494006868197489285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2955870329337912131659523 4433805494006868197489285)
                    ·
                      refine ⟨831338530126287787029241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4433805494006868197489285 831338530126287787029241)
                      ·
                        rfl

theorem cell23_1619026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_1619026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619026 prefixEnd_1619026 := by exact prefixLift 1619026
  have htrace : WordTrace (prefixWord ++ tailWord_1619026) baseStart_1619026 baseEnd_1619026 := by
    simpa [prefixWord, tailWord_1619026, baseEnd_1619026] using wordTrace_append hprefix tailTrace_1619026
  have hstable : (prefixWord ++ tailWord_1619026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619026).length < 2 ^ (prefixWord ++ tailWord_1619026).sum := by decide
  have hdescent : baseEnd_1619026 < baseStart_1619026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619032 : List Nat := [2, 1, 2, 2, 1, 3, 1, 11]
def baseStart_1619032 : Nat := 118140960795 + 1619032 * 2 ^ 59
def prefixEnd_1619032 : Nat := 4983230072969 + 3 ^ 40 * 1619032 * 2
def baseEnd_1619032 : Nat := 30790430037415361613119

theorem tailTrace_1619032 : CollatzResearch.WordTrace tailWord_1619032 prefixEnd_1619032 30790430037415361613119 := by
  unfold tailWord_1619032
  simp only [CollatzResearch.WordTrace]
  refine ⟨29525474135265523748365675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39367298847020698331154233 29525474135265523748365675)
  ·
    refine ⟨44288211202898285622548513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29525474135265523748365675 44288211202898285622548513)
    ·
      refine ⟨33216158402173714216911385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44288211202898285622548513 33216158402173714216911385)
      ·
        refine ⟨24912118801630285662683539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33216158402173714216911385 24912118801630285662683539)
        ·
          refine ⟨37368178202445428494025309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24912118801630285662683539 37368178202445428494025309)
          ·
            refine ⟨14013066825917035685259491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37368178202445428494025309 14013066825917035685259491)
            ·
              refine ⟨21019600238875553527889237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14013066825917035685259491 21019600238875553527889237)
              ·
                refine ⟨30790430037415361613119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 21019600238875553527889237 30790430037415361613119)
                ·
                  rfl

theorem cell23_1619032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 11].length) (baseStart_1619032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619032 prefixEnd_1619032 := by exact prefixLift 1619032
  have htrace : WordTrace (prefixWord ++ tailWord_1619032) baseStart_1619032 baseEnd_1619032 := by
    simpa [prefixWord, tailWord_1619032, baseEnd_1619032] using wordTrace_append hprefix tailTrace_1619032
  have hstable : (prefixWord ++ tailWord_1619032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619032).length < 2 ^ (prefixWord ++ tailWord_1619032).sum := by decide
  have hdescent : baseEnd_1619032 < baseStart_1619032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619039 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 4]
def baseStart_1619039 : Nat := 118140960795 + 1619039 * 2 ^ 59
def prefixEnd_1619039 : Nat := 4983230072969 + 3 ^ 40 * 1619039 * 2
def baseEnd_1619039 : Nat := 831345205374796236166681

theorem tailTrace_1619039 : CollatzResearch.WordTrace tailWord_1619039 prefixEnd_1619039 831345205374796236166681 := by
  unfold tailWord_1619039
  simp only [CollatzResearch.WordTrace]
  refine ⟨59051203581505687692236171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39367469054337125128157447 59051203581505687692236171)
  ·
    refine ⟨88576805372258531538354257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59051203581505687692236171 88576805372258531538354257)
    ·
      refine ⟨66432604029193898653765693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88576805372258531538354257 66432604029193898653765693)
      ·
        refine ⟨24912226510947711995162135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66432604029193898653765693 24912226510947711995162135)
        ·
          refine ⟨37368339766421567992743203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24912226510947711995162135 37368339766421567992743203)
          ·
            refine ⟨56052509649632351989114805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37368339766421567992743203 56052509649632351989114805)
            ·
              refine ⟨5254922779653032998979513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56052509649632351989114805 5254922779653032998979513)
              ·
                refine ⟨3941192084739774749234635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5254922779653032998979513 3941192084739774749234635)
                ·
                  refine ⟨5911788127109662123851953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941192084739774749234635 5911788127109662123851953)
                  ·
                    refine ⟨4433841095332246592888965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5911788127109662123851953 4433841095332246592888965)
                    ·
                      refine ⟨831345205374796236166681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4433841095332246592888965 831345205374796236166681)
                      ·
                        rfl

theorem cell23_1619039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_1619039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619039 prefixEnd_1619039 := by exact prefixLift 1619039
  have htrace : WordTrace (prefixWord ++ tailWord_1619039) baseStart_1619039 baseEnd_1619039 := by
    simpa [prefixWord, tailWord_1619039, baseEnd_1619039] using wordTrace_append hprefix tailTrace_1619039
  have hstable : (prefixWord ++ tailWord_1619039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619039).length < 2 ^ (prefixWord ++ tailWord_1619039).sum := by decide
  have hdescent : baseEnd_1619039 < baseStart_1619039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619053 : List Nat := [1, 5, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_1619053 : Nat := 118140960795 + 1619053 * 2 ^ 59
def prefixEnd_1619053 : Nat := 4983230072969 + 3 ^ 40 * 1619053 * 2
def baseEnd_1619053 : Nat := 277117464701319727130539

theorem tailTrace_1619053 : CollatzResearch.WordTrace tailWord_1619053 prefixEnd_1619053 277117464701319727130539 := by
  unfold tailWord_1619053
  simp only [CollatzResearch.WordTrace]
  refine ⟨59051714203454968083245813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39367809468969978722163875 59051714203454968083245813)
  ·
    refine ⟨5536098206573903257804295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59051714203454968083245813 5536098206573903257804295)
    ·
      refine ⟨8304147309860854886706443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5536098206573903257804295 8304147309860854886706443)
      ·
        refine ⟨12456220964791282330059665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8304147309860854886706443 12456220964791282330059665)
        ·
          refine ⟨9342165723593461747544749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12456220964791282330059665 9342165723593461747544749)
          ·
            refine ⟨3503312146347548155329281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9342165723593461747544749 3503312146347548155329281)
            ·
              refine ⟨2627484109760661116496961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3503312146347548155329281 2627484109760661116496961)
              ·
                refine ⟨1970613082320495837372721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2627484109760661116496961 1970613082320495837372721)
                ·
                  refine ⟨1477959811740371878029541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1970613082320495837372721 1477959811740371878029541)
                  ·
                    refine ⟨277117464701319727130539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1477959811740371878029541 277117464701319727130539)
                    ·
                      rfl

theorem cell23_1619053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_1619053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619053 prefixEnd_1619053 := by exact prefixLift 1619053
  have htrace : WordTrace (prefixWord ++ tailWord_1619053) baseStart_1619053 baseEnd_1619053 := by
    simpa [prefixWord, tailWord_1619053, baseEnd_1619053] using wordTrace_append hprefix tailTrace_1619053
  have hstable : (prefixWord ++ tailWord_1619053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619053).length < 2 ^ (prefixWord ++ tailWord_1619053).sum := by decide
  have hdescent : baseEnd_1619053 < baseStart_1619053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619076 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_1619076 : Nat := 118140960795 + 1619076 * 2 ^ 59
def prefixEnd_1619076 : Nat := 4983230072969 + 3 ^ 40 * 1619076 * 2
def baseEnd_1619076 : Nat := 831364204159012591404011

theorem tailTrace_1619076 : CollatzResearch.WordTrace tailWord_1619076 prefixEnd_1619076 831364204159012591404011 := by
  unfold tailWord_1619076
  simp only [CollatzResearch.WordTrace]
  refine ⟨29526276541185821505666541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39368368721581095340888721 29526276541185821505666541)
  ·
    refine ⟨11072353702944683064624953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29526276541185821505666541 11072353702944683064624953)
    ·
      refine ⟨8304265277208512298468715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11072353702944683064624953 8304265277208512298468715)
      ·
        refine ⟨12456397915812768447703073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8304265277208512298468715 12456397915812768447703073)
        ·
          refine ⟨9342298436859576335777305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12456397915812768447703073 9342298436859576335777305)
          ·
            refine ⟨7006723827644682251832979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9342298436859576335777305 7006723827644682251832979)
            ·
              refine ⟨10510085741467023377749469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7006723827644682251832979 10510085741467023377749469)
              ·
                refine ⟨3941282153050133766656051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10510085741467023377749469 3941282153050133766656051)
                ·
                  refine ⟨5911923229575200649984077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941282153050133766656051 5911923229575200649984077)
                  ·
                    refine ⟨2216971211090700243744029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5911923229575200649984077 2216971211090700243744029)
                    ·
                      refine ⟨831364204159012591404011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2216971211090700243744029 831364204159012591404011)
                      ·
                        rfl

theorem cell23_1619076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_1619076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619076 prefixEnd_1619076 := by exact prefixLift 1619076
  have htrace : WordTrace (prefixWord ++ tailWord_1619076) baseStart_1619076 baseEnd_1619076 := by
    simpa [prefixWord, tailWord_1619076, baseEnd_1619076] using wordTrace_append hprefix tailTrace_1619076
  have hstable : (prefixWord ++ tailWord_1619076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619076).length < 2 ^ (prefixWord ++ tailWord_1619076).sum := by decide
  have hdescent : baseEnd_1619076 < baseStart_1619076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619109 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 2, 6]
def baseStart_1619109 : Nat := 118140960795 + 1619109 * 2 ^ 59
def prefixEnd_1619109 : Nat := 4983230072969 + 3 ^ 40 * 1619109 * 2
def baseEnd_1619109 : Nat := 277127049673536987430453

theorem tailTrace_1619109 : CollatzResearch.WordTrace tailWord_1619109 prefixEnd_1619109 277127049673536987430453 := by
  unfold tailWord_1619109
  simp only [CollatzResearch.WordTrace]
  refine ⟨59053756691252089647284381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39369171127501393098189587 59053756691252089647284381)
  ·
    refine ⟨22145158759219533617731643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59053756691252089647284381 22145158759219533617731643)
    ·
      refine ⟨33217738138829300426597465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22145158759219533617731643 33217738138829300426597465)
      ·
        refine ⟨24913303604121975319948099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33217738138829300426597465 24913303604121975319948099)
        ·
          refine ⟨37369955406182962979922149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24913303604121975319948099 37369955406182962979922149)
          ·
            refine ⟨7006866638659305558735403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37369955406182962979922149 7006866638659305558735403)
            ·
              refine ⟨10510299957988958338103105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7006866638659305558735403 10510299957988958338103105)
              ·
                refine ⟨7882724968491718753577329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10510299957988958338103105 7882724968491718753577329)
                ·
                  refine ⟨5912043726368789065182997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7882724968491718753577329 5912043726368789065182997)
                  ·
                    refine ⟨277127049673536987430453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5912043726368789065182997 277127049673536987430453)
                    ·
                      rfl

theorem cell23_1619109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_1619109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619109 prefixEnd_1619109 := by exact prefixLift 1619109
  have htrace : WordTrace (prefixWord ++ tailWord_1619109) baseStart_1619109 baseEnd_1619109 := by
    simpa [prefixWord, tailWord_1619109, baseEnd_1619109] using wordTrace_append hprefix tailTrace_1619109
  have hstable : (prefixWord ++ tailWord_1619109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619109).length < 2 ^ (prefixWord ++ tailWord_1619109).sum := by decide
  have hdescent : baseEnd_1619109 < baseStart_1619109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619119 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 3]
def baseStart_1619119 : Nat := 118140960795 + 1619119 * 2 ^ 59
def prefixEnd_1619119 : Nat := 4983230072969 + 3 ^ 40 * 1619119 * 2
def baseEnd_1619119 : Nat := 831386283827155923166313

theorem tailTrace_1619119 : CollatzResearch.WordTrace tailWord_1619119 prefixEnd_1619119 831386283827155923166313 := by
  unfold tailWord_1619119
  simp only [CollatzResearch.WordTrace]
  refine ⟨59054121421215861355148411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39369414280810574236765607 59054121421215861355148411)
  ·
    refine ⟨88581182131823792032722617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59054121421215861355148411 88581182131823792032722617)
    ·
      refine ⟨66435886598867844024541963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88581182131823792032722617 66435886598867844024541963)
      ·
        refine ⟨99653829898301766036812945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66435886598867844024541963 99653829898301766036812945)
        ·
          refine ⟨74740372423726324527609709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99653829898301766036812945 74740372423726324527609709)
          ·
            refine ⟨28027639658897371697853641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74740372423726324527609709 28027639658897371697853641)
            ·
              refine ⟨21020729744173028773390231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28027639658897371697853641 21020729744173028773390231)
              ·
                refine ⟨31531094616259543160085347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21020729744173028773390231 31531094616259543160085347)
                ·
                  refine ⟨47296641924389314740128021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31531094616259543160085347 47296641924389314740128021)
                  ·
                    refine ⟨2217030090205749128443501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47296641924389314740128021 2217030090205749128443501)
                    ·
                      refine ⟨831386283827155923166313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2217030090205749128443501 831386283827155923166313)
                      ·
                        rfl

theorem cell23_1619119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 3].length) (baseStart_1619119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619119 prefixEnd_1619119 := by exact prefixLift 1619119
  have htrace : WordTrace (prefixWord ++ tailWord_1619119) baseStart_1619119 baseEnd_1619119 := by
    simpa [prefixWord, tailWord_1619119, baseEnd_1619119] using wordTrace_append hprefix tailTrace_1619119
  have hstable : (prefixWord ++ tailWord_1619119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619119).length < 2 ^ (prefixWord ++ tailWord_1619119).sum := by decide
  have hdescent : baseEnd_1619119 < baseStart_1619119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619133 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 1, 4, 2]
def baseStart_1619133 : Nat := 118140960795 + 1619133 * 2 ^ 59
def prefixEnd_1619133 : Nat := 4983230072969 + 3 ^ 40 * 1619133 * 2
def baseEnd_1619133 : Nat := 831393472556318868391249

theorem tailTrace_1619133 : CollatzResearch.WordTrace tailWord_1619133 prefixEnd_1619133 831393472556318868391249 := by
  unfold tailWord_1619133
  simp only [CollatzResearch.WordTrace]
  refine ⟨59054632043165141746158053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39369754695443427830772035 59054632043165141746158053)
  ·
    refine ⟨11072743508093464077404635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59054632043165141746158053 11072743508093464077404635)
    ·
      refine ⟨16609115262140196116106953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11072743508093464077404635 16609115262140196116106953)
      ·
        refine ⟨12456836446605147087080215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16609115262140196116106953 12456836446605147087080215)
        ·
          refine ⟨18685254669907720630620323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12456836446605147087080215 18685254669907720630620323)
          ·
            refine ⟨28027882004861580945930485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18685254669907720630620323 28027882004861580945930485)
            ·
              refine ⟨2627613937955773213680983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28027882004861580945930485 2627613937955773213680983)
              ·
                refine ⟨3941420906933659820521475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2627613937955773213680983 3941420906933659820521475)
                ·
                  refine ⟨5912131360400489730782213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941420906933659820521475 5912131360400489730782213)
                  ·
                    refine ⟨1108524630075091824521665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5912131360400489730782213 1108524630075091824521665)
                    ·
                      refine ⟨831393472556318868391249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1108524630075091824521665 831393472556318868391249)
                      ·
                        rfl

theorem cell23_1619133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_1619133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619133 prefixEnd_1619133 := by exact prefixLift 1619133
  have htrace : WordTrace (prefixWord ++ tailWord_1619133) baseStart_1619133 baseEnd_1619133 := by
    simpa [prefixWord, tailWord_1619133, baseEnd_1619133] using wordTrace_append hprefix tailTrace_1619133
  have hstable : (prefixWord ++ tailWord_1619133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619133).length < 2 ^ (prefixWord ++ tailWord_1619133).sum := by decide
  have hdescent : baseEnd_1619133 < baseStart_1619133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619137 : List Nat := [1, 2, 6, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_1619137 : Nat := 118140960795 + 1619137 * 2 ^ 59
def prefixEnd_1619137 : Nat := 4983230072969 + 3 ^ 40 * 1619137 * 2
def baseEnd_1619137 : Nat := 831395526478936852741231

theorem tailTrace_1619137 : CollatzResearch.WordTrace tailWord_1619137 prefixEnd_1619137 831395526478936852741231 := by
  unfold tailWord_1619137
  simp only [CollatzResearch.WordTrace]
  refine ⟨59054777935150650429303665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39369851956767100286202443 59054777935150650429303665)
  ·
    refine ⟨44291083451362987821977749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59054777935150650429303665 44291083451362987821977749)
    ·
      refine ⟨2076144536782640054155207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44291083451362987821977749 2076144536782640054155207)
      ·
        refine ⟨3114216805173960081232811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2076144536782640054155207 3114216805173960081232811)
        ·
          refine ⟨4671325207760940121849217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3114216805173960081232811 4671325207760940121849217)
          ·
            refine ⟨3503493905820705091386913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4671325207760940121849217 3503493905820705091386913)
            ·
              refine ⟨2627620429365528818540185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3503493905820705091386913 2627620429365528818540185)
              ·
                refine ⟨1970715322024146613905139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2627620429365528818540185 1970715322024146613905139)
                ·
                  refine ⟨2956072983036219920857709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1970715322024146613905139 2956072983036219920857709)
                  ·
                    refine ⟨1108527368638582470321641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2956072983036219920857709 1108527368638582470321641)
                    ·
                      refine ⟨831395526478936852741231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1108527368638582470321641 831395526478936852741231)
                      ·
                        rfl

theorem cell23_1619137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_1619137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619137 prefixEnd_1619137 := by exact prefixLift 1619137
  have htrace : WordTrace (prefixWord ++ tailWord_1619137) baseStart_1619137 baseEnd_1619137 := by
    simpa [prefixWord, tailWord_1619137, baseEnd_1619137] using wordTrace_append hprefix tailTrace_1619137
  have hstable : (prefixWord ++ tailWord_1619137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619137).length < 2 ^ (prefixWord ++ tailWord_1619137).sum := by decide
  have hdescent : baseEnd_1619137 < baseStart_1619137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619173 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 7]
def baseStart_1619173 : Nat := 118140960795 + 1619173 * 2 ^ 59
def prefixEnd_1619173 : Nat := 4983230072969 + 3 ^ 40 * 1619173 * 2
def baseEnd_1619173 : Nat := 92379334642499856876785

theorem tailTrace_1619173 : CollatzResearch.WordTrace tailWord_1619173 prefixEnd_1619173 92379334642499856876785 := by
  unfold tailWord_1619173
  simp only [CollatzResearch.WordTrace]
  refine ⟨59056090963020228577614173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39370727308680152385076115 59056090963020228577614173)
  ·
    refine ⟨22146034111132585716605315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59056090963020228577614173 22146034111132585716605315)
    ·
      refine ⟨33219051166698878574907973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22146034111132585716605315 33219051166698878574907973)
      ·
        refine ⟨6228572093756039732795245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33219051166698878574907973 6228572093756039732795245)
        ·
          refine ⟨2335714535158514899798217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6228572093756039732795245 2335714535158514899798217)
          ·
            refine ⟨1751785901368886174848663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2335714535158514899798217 1751785901368886174848663)
            ·
              refine ⟨2627678852053329262272995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1751785901368886174848663 2627678852053329262272995)
              ·
                refine ⟨3941518278079993893409493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2627678852053329262272995 3941518278079993893409493)
                ·
                  refine ⟨92379334642499856876785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3941518278079993893409493 92379334642499856876785)
                  ·
                    rfl

theorem cell23_1619173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 7].length) (baseStart_1619173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619173 prefixEnd_1619173 := by exact prefixLift 1619173
  have htrace : WordTrace (prefixWord ++ tailWord_1619173) baseStart_1619173 baseEnd_1619173 := by
    simpa [prefixWord, tailWord_1619173, baseEnd_1619173] using wordTrace_append hprefix tailTrace_1619173
  have hstable : (prefixWord ++ tailWord_1619173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619173).length < 2 ^ (prefixWord ++ tailWord_1619173).sum := by decide
  have hdescent : baseEnd_1619173 < baseStart_1619173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619179 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 7]
def baseStart_1619179 : Nat := 118140960795 + 1619179 * 2 ^ 59
def prefixEnd_1619179 : Nat := 4983230072969 + 3 ^ 40 * 1619179 * 2
def baseEnd_1619179 : Nat := 831417092666425688416037

theorem tailTrace_1619179 : CollatzResearch.WordTrace tailWord_1619179 prefixEnd_1619179 831417092666425688416037 := by
  unfold tailWord_1619179
  simp only [CollatzResearch.WordTrace]
  refine ⟨59056309800998491602332591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39370873200665661068221727 59056309800998491602332591)
  ·
    refine ⟨88584464701497737403498887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59056309800998491602332591 88584464701497737403498887)
    ·
      refine ⟨132876697052246606105248331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88584464701497737403498887 132876697052246606105248331)
      ·
        refine ⟨199315045578369909157872497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132876697052246606105248331 199315045578369909157872497)
        ·
          refine ⟨149486284183777431868404373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199315045578369909157872497 149486284183777431868404373)
          ·
            refine ⟨7007169571114567118831455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 149486284183777431868404373 7007169571114567118831455)
            ·
              refine ⟨10510754356671850678247183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7007169571114567118831455 10510754356671850678247183)
              ·
                refine ⟨15766131535007776017370775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10510754356671850678247183 15766131535007776017370775)
                ·
                  refine ⟨23649197302511664026056163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15766131535007776017370775 23649197302511664026056163)
                  ·
                    refine ⟨35473795953767496039084245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23649197302511664026056163 35473795953767496039084245)
                    ·
                      refine ⟨831417092666425688416037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35473795953767496039084245 831417092666425688416037)
                      ·
                        rfl

theorem cell23_1619179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 7].length) (baseStart_1619179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619179 prefixEnd_1619179 := by exact prefixLift 1619179
  have htrace : WordTrace (prefixWord ++ tailWord_1619179) baseStart_1619179 baseEnd_1619179 := by
    simpa [prefixWord, tailWord_1619179, baseEnd_1619179] using wordTrace_append hprefix tailTrace_1619179
  have hstable : (prefixWord ++ tailWord_1619179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619179).length < 2 ^ (prefixWord ++ tailWord_1619179).sum := by decide
  have hdescent : baseEnd_1619179 < baseStart_1619179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619188 : List Nat := [2, 6, 1, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_1619188 : Nat := 118140960795 + 1619188 * 2 ^ 59
def prefixEnd_1619188 : Nat := 4983230072969 + 3 ^ 40 * 1619188 * 2
def baseEnd_1619188 : Nat := 831421713992316153203497

theorem tailTrace_1619188 : CollatzResearch.WordTrace tailWord_1619188 prefixEnd_1619188 831421713992316153203497 := by
  unfold tailWord_1619188
  simp only [CollatzResearch.WordTrace]
  refine ⟨29528319028982943069705109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39371092038643924092940145 29528319028982943069705109)
  ·
    refine ⟨1384139954483575456392427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29528319028982943069705109 1384139954483575456392427)
    ·
      refine ⟨2076209931725363184588641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1384139954483575456392427 2076209931725363184588641)
      ·
        refine ⟨1557157448794022388441481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2076209931725363184588641 1557157448794022388441481)
        ·
          refine ⟨1167868086595516791331111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1557157448794022388441481 1167868086595516791331111)
          ·
            refine ⟨1751802129893275186996667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167868086595516791331111 1751802129893275186996667)
            ·
              refine ⟨2627703194839912780495001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1751802129893275186996667 2627703194839912780495001)
              ·
                refine ⟨1970777396129934585371251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2627703194839912780495001 1970777396129934585371251)
                ·
                  refine ⟨2956166094194901878056877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1970777396129934585371251 2956166094194901878056877)
                  ·
                    refine ⟨1108562285323088204271329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2956166094194901878056877 1108562285323088204271329)
                    ·
                      refine ⟨831421713992316153203497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1108562285323088204271329 831421713992316153203497)
                      ·
                        rfl

theorem cell23_1619188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_1619188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619188 prefixEnd_1619188 := by exact prefixLift 1619188
  have htrace : WordTrace (prefixWord ++ tailWord_1619188) baseStart_1619188 baseEnd_1619188 := by
    simpa [prefixWord, tailWord_1619188, baseEnd_1619188] using wordTrace_append hprefix tailTrace_1619188
  have hstable : (prefixWord ++ tailWord_1619188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619188).length < 2 ^ (prefixWord ++ tailWord_1619188).sum := by decide
  have hdescent : baseEnd_1619188 < baseStart_1619188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619223 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 2, 4, 2]
def baseStart_1619223 : Nat := 118140960795 + 1619223 * 2 ^ 59
def prefixEnd_1619223 : Nat := 4983230072969 + 3 ^ 40 * 1619223 * 2
def baseEnd_1619223 : Nat := 831439685815223516265835

theorem tailTrace_1619223 : CollatzResearch.WordTrace tailWord_1619223 prefixEnd_1619223 831439685815223516265835 := by
  unfold tailWord_1619223
  simp only [CollatzResearch.WordTrace]
  refine ⟨59057914612839087116934323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39371943075226058077956215 59057914612839087116934323)
  ·
    refine ⟨88586871919258630675401485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59057914612839087116934323 88586871919258630675401485)
    ·
      refine ⟨33220076969721986503275557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88586871919258630675401485 33220076969721986503275557)
      ·
        refine ⟨6228764431822872469364167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33220076969721986503275557 6228764431822872469364167)
        ·
          refine ⟨9343146647734308704046251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6228764431822872469364167 9343146647734308704046251)
          ·
            refine ⟨14014719971601463056069377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9343146647734308704046251 14014719971601463056069377)
            ·
              refine ⟨10511039978701097292052033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14014719971601463056069377 10511039978701097292052033)
              ·
                refine ⟨7883279984025822969039025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10511039978701097292052033 7883279984025822969039025)
                ·
                  refine ⟨5912459988019367226779269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7883279984025822969039025 5912459988019367226779269)
                  ·
                    refine ⟨1108586247753631355021113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5912459988019367226779269 1108586247753631355021113)
                    ·
                      refine ⟨831439685815223516265835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1108586247753631355021113 831439685815223516265835)
                      ·
                        rfl

theorem cell23_1619223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_1619223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619223 prefixEnd_1619223 := by exact prefixLift 1619223
  have htrace : WordTrace (prefixWord ++ tailWord_1619223) baseStart_1619223 baseEnd_1619223 := by
    simpa [prefixWord, tailWord_1619223, baseEnd_1619223] using wordTrace_append hprefix tailTrace_1619223
  have hstable : (prefixWord ++ tailWord_1619223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619223).length < 2 ^ (prefixWord ++ tailWord_1619223).sum := by decide
  have hdescent : baseEnd_1619223 < baseStart_1619223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619240 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_1619240 : Nat := 118140960795 + 1619240 * 2 ^ 59
def prefixEnd_1619240 : Nat := 4983230072969 + 3 ^ 40 * 1619240 * 2
def baseEnd_1619240 : Nat := 831448414986349949753257

theorem tailTrace_1619240 : CollatzResearch.WordTrace tailWord_1619240 prefixEnd_1619240 831448414986349949753257 := by
  unfold tailWord_1619240
  simp only [CollatzResearch.WordTrace]
  refine ⟨29529267326888749510151587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39372356435851666013535449 29529267326888749510151587)
  ·
    refine ⟨44293900990333124265227381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29529267326888749510151587 44293900990333124265227381)
    ·
      refine ⟨4152553217843730399865067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44293900990333124265227381 4152553217843730399865067)
      ·
        refine ⟨6228829826765595599797601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4152553217843730399865067 6228829826765595599797601)
        ·
          refine ⟨4671622370074196699848201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6228829826765595599797601 4671622370074196699848201)
          ·
            refine ⟨3503716777555647524886151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4671622370074196699848201 3503716777555647524886151)
            ·
              refine ⟨5255575166333471287329227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3503716777555647524886151 5255575166333471287329227)
              ·
                refine ⟨7883362749500206930993841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5255575166333471287329227 7883362749500206930993841)
                ·
                  refine ⟨5912522062125155198245381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7883362749500206930993841 5912522062125155198245381)
                  ·
                    refine ⟨1108597886648466599671009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5912522062125155198245381 1108597886648466599671009)
                    ·
                      refine ⟨831448414986349949753257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1108597886648466599671009 831448414986349949753257)
                      ·
                        rfl

theorem cell23_1619240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_1619240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619240 prefixEnd_1619240 := by exact prefixLift 1619240
  have htrace : WordTrace (prefixWord ++ tailWord_1619240) baseStart_1619240 baseEnd_1619240 := by
    simpa [prefixWord, tailWord_1619240, baseEnd_1619240] using wordTrace_append hprefix tailTrace_1619240
  have hstable : (prefixWord ++ tailWord_1619240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619240).length < 2 ^ (prefixWord ++ tailWord_1619240).sum := by decide
  have hdescent : baseEnd_1619240 < baseStart_1619240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619254 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_1619254 : Nat := 118140960795 + 1619254 * 2 ^ 59
def prefixEnd_1619254 : Nat := 4983230072969 + 3 ^ 40 * 1619254 * 2
def baseEnd_1619254 : Nat := 277151867905170964992731

theorem tailTrace_1619254 : CollatzResearch.WordTrace tailWord_1619254 prefixEnd_1619254 277151867905170964992731 := by
  unfold tailWord_1619254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3691190329732923713207051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39372696850484519607541877 3691190329732923713207051)
  ·
    refine ⟨5536785494599385569810577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3691190329732923713207051 5536785494599385569810577)
    ·
      refine ⟨4152589120949539177357933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5536785494599385569810577 4152589120949539177357933)
      ·
        refine ⟨1557220920356077191509225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4152589120949539177357933 1557220920356077191509225)
        ·
          refine ⟨1167915690267057893631919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1557220920356077191509225 1167915690267057893631919)
          ·
            refine ⟨1751873535400586840447879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167915690267057893631919 1751873535400586840447879)
            ·
              refine ⟨2627810303100880260671819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1751873535400586840447879 2627810303100880260671819)
              ·
                refine ⟨3941715454651320391007729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2627810303100880260671819 3941715454651320391007729)
                ·
                  refine ⟨2956286590988490293255797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3941715454651320391007729 2956286590988490293255797)
                  ·
                    refine ⟨277151867905170964992731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2956286590988490293255797 277151867905170964992731)
                    ·
                      rfl

theorem cell23_1619254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_1619254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619254 prefixEnd_1619254 := by exact prefixLift 1619254
  have htrace : WordTrace (prefixWord ++ tailWord_1619254) baseStart_1619254 baseEnd_1619254 := by
    simpa [prefixWord, tailWord_1619254, baseEnd_1619254] using wordTrace_append hprefix tailTrace_1619254
  have hstable : (prefixWord ++ tailWord_1619254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619254).length < 2 ^ (prefixWord ++ tailWord_1619254).sum := by decide
  have hdescent : baseEnd_1619254 < baseStart_1619254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619257 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 2, 1, 4]
def baseStart_1619257 : Nat := 118140960795 + 1619257 * 2 ^ 59
def prefixEnd_1619257 : Nat := 4983230072969 + 3 ^ 40 * 1619257 * 2
def baseEnd_1619257 : Nat := 831457144157476383240679

theorem tailTrace_1619257 : CollatzResearch.WordTrace tailWord_1619257 prefixEnd_1619257 831457144157476383240679 := by
  unfold tailWord_1619257
  simp only [CollatzResearch.WordTrace]
  refine ⟨59059154694715910923672025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39372769796477273949114683 59059154694715910923672025)
  ·
    refine ⟨44294366021036933192754019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59059154694715910923672025 44294366021036933192754019)
    ·
      refine ⟨66441549031555399789131029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44294366021036933192754019 66441549031555399789131029)
      ·
        refine ⟨3114447610854159365115517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66441549031555399789131029 3114447610854159365115517)
        ·
          refine ⟨1167917854070309761918319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3114447610854159365115517 1167917854070309761918319)
          ·
            refine ⟨1751876781105464642877479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167917854070309761918319 1751876781105464642877479)
            ·
              refine ⟨2627815171658196964316219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1751876781105464642877479 2627815171658196964316219)
              ·
                refine ⟨3941722757487295446474329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2627815171658196964316219 3941722757487295446474329)
                ·
                  refine ⟨2956292068115471584855747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3941722757487295446474329 2956292068115471584855747)
                  ·
                    refine ⟨4434438102173207377283621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2956292068115471584855747 4434438102173207377283621)
                    ·
                      refine ⟨831457144157476383240679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4434438102173207377283621 831457144157476383240679)
                      ·
                        rfl

theorem cell23_1619257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_1619257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619257 prefixEnd_1619257 := by exact prefixLift 1619257
  have htrace : WordTrace (prefixWord ++ tailWord_1619257) baseStart_1619257 baseEnd_1619257 := by
    simpa [prefixWord, tailWord_1619257, baseEnd_1619257] using wordTrace_append hprefix tailTrace_1619257
  have hstable : (prefixWord ++ tailWord_1619257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619257).length < 2 ^ (prefixWord ++ tailWord_1619257).sum := by decide
  have hdescent : baseEnd_1619257 < baseStart_1619257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619260 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 2, 2, 3]
def baseStart_1619260 : Nat := 118140960795 + 1619260 * 2 ^ 59
def prefixEnd_1619260 : Nat := 4983230072969 + 3 ^ 40 * 1619260 * 2
def baseEnd_1619260 : Nat := 831458684599439871503165

theorem tailTrace_1619260 : CollatzResearch.WordTrace tailWord_1619260 prefixEnd_1619260 831458684599439871503165 := by
  unfold tailWord_1619260
  simp only [CollatzResearch.WordTrace]
  refine ⟨29529632056852521218015617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39372842742470028290687489 29529632056852521218015617)
  ·
    refine ⟨22147224042639390913511713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29529632056852521218015617 22147224042639390913511713)
    ·
      refine ⟨16610418031979543185133785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22147224042639390913511713 16610418031979543185133785)
      ·
        refine ⟨12457813523984657388850339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16610418031979543185133785 12457813523984657388850339)
        ·
          refine ⟨18686720285976986083275509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12457813523984657388850339 18686720285976986083275509)
          ·
            refine ⟨1751880026810342445307079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18686720285976986083275509 1751880026810342445307079)
            ·
              refine ⟨2627820040215513667960619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1751880026810342445307079 2627820040215513667960619)
              ·
                refine ⟨3941730060323270501940929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2627820040215513667960619 3941730060323270501940929)
                ·
                  refine ⟨2956297545242452876455697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3941730060323270501940929 2956297545242452876455697)
                  ·
                    refine ⟨2217223158931839657341773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2956297545242452876455697 2217223158931839657341773)
                    ·
                      refine ⟨831458684599439871503165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2217223158931839657341773 831458684599439871503165)
                      ·
                        rfl

theorem cell23_1619260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_1619260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619260 prefixEnd_1619260 := by exact prefixLift 1619260
  have htrace : WordTrace (prefixWord ++ tailWord_1619260) baseStart_1619260 baseEnd_1619260 := by
    simpa [prefixWord, tailWord_1619260, baseEnd_1619260] using wordTrace_append hprefix tailTrace_1619260
  have hstable : (prefixWord ++ tailWord_1619260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619260).length < 2 ^ (prefixWord ++ tailWord_1619260).sum := by decide
  have hdescent : baseEnd_1619260 < baseStart_1619260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619283 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 4, 3, 2]
def baseStart_1619283 : Nat := 118140960795 + 1619283 * 2 ^ 59
def prefixEnd_1619283 : Nat := 4983230072969 + 3 ^ 40 * 1619283 * 2
def baseEnd_1619283 : Nat := 831470494654493281515559

theorem tailTrace_1619283 : CollatzResearch.WordTrace tailWord_1619283 prefixEnd_1619283 831470494654493281515559 := by
  unfold tailWord_1619283
  simp only [CollatzResearch.WordTrace]
  refine ⟨59060102992621717364118503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39373401995081144909412335 59060102992621717364118503)
  ·
    refine ⟨88590154488932576046177755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59060102992621717364118503 88590154488932576046177755)
    ·
      refine ⟨132885231733398864069266633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88590154488932576046177755 132885231733398864069266633)
      ·
        refine ⟨99663923800049148051949975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132885231733398864069266633 99663923800049148051949975)
        ·
          refine ⟨149495885700073722077924963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99663923800049148051949975 149495885700073722077924963)
          ·
            refine ⟨224243828550110583116887445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149495885700073722077924963 224243828550110583116887445)
            ·
              refine ⟨10511429463286433583604099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 224243828550110583116887445 10511429463286433583604099)
              ·
                refine ⟨15767144194929650375406149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10511429463286433583604099 15767144194929650375406149)
                ·
                  refine ⟨2956339536549309445388653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15767144194929650375406149 2956339536549309445388653)
                  ·
                    refine ⟨1108627326205991042020745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2956339536549309445388653 1108627326205991042020745)
                    ·
                      refine ⟨831470494654493281515559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1108627326205991042020745 831470494654493281515559)
                      ·
                        rfl

theorem cell23_1619283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 3, 2].length) (baseStart_1619283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619283 prefixEnd_1619283 := by exact prefixLift 1619283
  have htrace : WordTrace (prefixWord ++ tailWord_1619283) baseStart_1619283 baseEnd_1619283 := by
    simpa [prefixWord, tailWord_1619283, baseEnd_1619283] using wordTrace_append hprefix tailTrace_1619283
  have hstable : (prefixWord ++ tailWord_1619283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619283).length < 2 ^ (prefixWord ++ tailWord_1619283).sum := by decide
  have hdescent : baseEnd_1619283 < baseStart_1619283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619313 : List Nat := [1, 2, 2, 2, 1, 2, 3, 4, 1, 1, 4]
def baseStart_1619313 : Nat := 118140960795 + 1619313 * 2 ^ 59
def prefixEnd_1619313 : Nat := 4983230072969 + 3 ^ 40 * 1619313 * 2
def baseEnd_1619313 : Nat := 831485899074128164140421

theorem tailTrace_1619313 : CollatzResearch.WordTrace tailWord_1619313 prefixEnd_1619313 831485899074128164140421 := by
  unfold tailWord_1619313
  simp only [CollatzResearch.WordTrace]
  refine ⟨59061197182513032487710593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39374131455008688325140395 59061197182513032487710593)
  ·
    refine ⟨44295897886884774365782945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59061197182513032487710593 44295897886884774365782945)
    ·
      refine ⟨33221923415163580774337209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44295897886884774365782945 33221923415163580774337209)
      ·
        refine ⟨24916442561372685580752907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33221923415163580774337209 24916442561372685580752907)
        ·
          refine ⟨37374663842059028371129361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24916442561372685580752907 37374663842059028371129361)
          ·
            refine ⟨28030997881544271278347021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37374663842059028371129361 28030997881544271278347021)
            ·
              refine ⟨10511624205579101729380133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28030997881544271278347021 10511624205579101729380133)
              ·
                refine ⟨1970929538546081574258775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10511624205579101729380133 1970929538546081574258775)
                ·
                  refine ⟨2956394307819122361388163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1970929538546081574258775 2956394307819122361388163)
                  ·
                    refine ⟨4434591461728683542082245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2956394307819122361388163 4434591461728683542082245)
                    ·
                      refine ⟨831485899074128164140421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4434591461728683542082245 831485899074128164140421)
                      ·
                        rfl

theorem cell23_1619313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_1619313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619313 prefixEnd_1619313 := by exact prefixLift 1619313
  have htrace : WordTrace (prefixWord ++ tailWord_1619313) baseStart_1619313 baseEnd_1619313 := by
    simpa [prefixWord, tailWord_1619313, baseEnd_1619313] using wordTrace_append hprefix tailTrace_1619313
  have hstable : (prefixWord ++ tailWord_1619313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619313).length < 2 ^ (prefixWord ++ tailWord_1619313).sum := by decide
  have hdescent : baseEnd_1619313 < baseStart_1619313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619336 : List Nat := [2, 1, 3, 3, 1, 2, 11]
def baseStart_1619336 : Nat := 118140960795 + 1619336 * 2 ^ 59
def prefixEnd_1619336 : Nat := 4983230072969 + 3 ^ 40 * 1619336 * 2
def baseEnd_1619336 : Nat := 10265403816409649063615

theorem tailTrace_1619336 : CollatzResearch.WordTrace tailWord_1619336 prefixEnd_1619336 10265403816409649063615 := by
  unfold tailWord_1619336
  simp only [CollatzResearch.WordTrace]
  refine ⟨29531018030714853707898931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39374690707619804943865241 29531018030714853707898931)
  ·
    refine ⟨44296527046072280561848397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29531018030714853707898931 44296527046072280561848397)
    ·
      refine ⟨16611197642277105210693149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44296527046072280561848397 16611197642277105210693149)
      ·
        refine ⟨6229199115853914454009931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16611197642277105210693149 6229199115853914454009931)
        ·
          refine ⟨9343798673780871681014897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6229199115853914454009931 9343798673780871681014897)
          ·
            refine ⟨7007849005335653760761173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9343798673780871681014897 7007849005335653760761173)
            ·
              refine ⟨10265403816409649063615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7007849005335653760761173 10265403816409649063615)
              ·
                rfl

theorem cell23_1619336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 11].length) (baseStart_1619336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619336 prefixEnd_1619336 := by exact prefixLift 1619336
  have htrace : WordTrace (prefixWord ++ tailWord_1619336) baseStart_1619336 baseEnd_1619336 := by
    simpa [prefixWord, tailWord_1619336, baseEnd_1619336] using wordTrace_append hprefix tailTrace_1619336
  have hstable : (prefixWord ++ tailWord_1619336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619336).length < 2 ^ (prefixWord ++ tailWord_1619336).sum := by decide
  have hdescent : baseEnd_1619336 < baseStart_1619336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619357 : List Nat := [1, 4, 2, 1, 3, 1, 4, 1, 2, 4]
def baseStart_1619357 : Nat := 118140960795 + 1619357 * 2 ^ 59
def prefixEnd_1619357 : Nat := 4983230072969 + 3 ^ 40 * 1619357 * 2
def baseEnd_1619357 : Nat := 277169497407641997330073

theorem tailTrace_1619357 : CollatzResearch.WordTrace tailWord_1619357 prefixEnd_1619357 277169497407641997330073 := by
  unfold tailWord_1619357
  simp only [CollatzResearch.WordTrace]
  refine ⟨59062801994353628002312325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39375201329569085334874883 59062801994353628002312325)
  ·
    refine ⟨11074275373941305250433561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59062801994353628002312325 11074275373941305250433561)
    ·
      refine ⟨8305706530455978937825171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11074275373941305250433561 8305706530455978937825171)
      ·
        refine ⟨12458559795683968406737757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8305706530455978937825171 12458559795683968406737757)
        ·
          refine ⟨4671959923381488152526659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12458559795683968406737757 4671959923381488152526659)
          ·
            refine ⟨7007939885072232228789989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4671959923381488152526659 7007939885072232228789989)
            ·
              refine ⟨1313988728451043542898123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7007939885072232228789989 1313988728451043542898123)
              ·
                refine ⟨1970983092676565314347185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313988728451043542898123 1970983092676565314347185)
                ·
                  refine ⟨1478237319507423985760389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1970983092676565314347185 1478237319507423985760389)
                  ·
                    refine ⟨277169497407641997330073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1478237319507423985760389 277169497407641997330073)
                    ·
                      rfl

theorem cell23_1619357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_1619357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619357 prefixEnd_1619357 := by exact prefixLift 1619357
  have htrace : WordTrace (prefixWord ++ tailWord_1619357) baseStart_1619357 baseEnd_1619357 := by
    simpa [prefixWord, tailWord_1619357, baseEnd_1619357] using wordTrace_append hprefix tailTrace_1619357
  have hstable : (prefixWord ++ tailWord_1619357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619357).length < 2 ^ (prefixWord ++ tailWord_1619357).sum := by decide
  have hdescent : baseEnd_1619357 < baseStart_1619357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619363 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 3]
def baseStart_1619363 : Nat := 118140960795 + 1619363 * 2 ^ 59
def prefixEnd_1619363 : Nat := 4983230072969 + 3 ^ 40 * 1619363 * 2
def baseEnd_1619363 : Nat := 831511573106852968515191

theorem tailTrace_1619363 : CollatzResearch.WordTrace tailWord_1619363 prefixEnd_1619363 831511573106852968515191 := by
  unfold tailWord_1619363
  simp only [CollatzResearch.WordTrace]
  refine ⟨59063020832331891027030743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39375347221554594018020495 59063020832331891027030743)
  ·
    refine ⟨88594531248497836540546115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59063020832331891027030743 88594531248497836540546115)
    ·
      refine ⟨132891796872746754810819173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88594531248497836540546115 132891796872746754810819173)
      ·
        refine ⟨24917211913640016527028595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132891796872746754810819173 24917211913640016527028595)
        ·
          refine ⟨37375817870460024790542893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24917211913640016527028595 37375817870460024790542893)
          ·
            refine ⟨14015931701422509296453585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37375817870460024790542893 14015931701422509296453585)
            ·
              refine ⟨10511948776066881972340189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14015931701422509296453585 10511948776066881972340189)
              ·
                refine ⟨3941980791025080739627571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10511948776066881972340189 3941980791025080739627571)
                ·
                  refine ⟨5912971186537621109441357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941980791025080739627571 5912971186537621109441357)
                  ·
                    refine ⟨2217364194951607916040509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5912971186537621109441357 2217364194951607916040509)
                    ·
                      refine ⟨831511573106852968515191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2217364194951607916040509 831511573106852968515191)
                      ·
                        rfl

theorem cell23_1619363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_1619363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619363 prefixEnd_1619363 := by exact prefixLift 1619363
  have htrace : WordTrace (prefixWord ++ tailWord_1619363) baseStart_1619363 baseEnd_1619363 := by
    simpa [prefixWord, tailWord_1619363, baseEnd_1619363] using wordTrace_append hprefix tailTrace_1619363
  have hstable : (prefixWord ++ tailWord_1619363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619363).length < 2 ^ (prefixWord ++ tailWord_1619363).sum := by decide
  have hdescent : baseEnd_1619363 < baseStart_1619363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619376 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 5]
def baseStart_1619376 : Nat := 118140960795 + 1619376 * 2 ^ 59
def prefixEnd_1619376 : Nat := 4983230072969 + 3 ^ 40 * 1619376 * 2
def baseEnd_1619376 : Nat := 831518248355361417652631

theorem tailTrace_1619376 : CollatzResearch.WordTrace tailWord_1619376 prefixEnd_1619376 831518248355361417652631 := by
  unfold tailWord_1619376
  simp only [CollatzResearch.WordTrace]
  refine ⟨29531747490642397123626991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39375663320856529498169321 29531747490642397123626991)
  ·
    refine ⟨44297621235963595685440487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29531747490642397123626991 44297621235963595685440487)
    ·
      refine ⟨66446431853945393528160731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44297621235963595685440487 66446431853945393528160731)
      ·
        refine ⟨99669647780918090292241097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66446431853945393528160731 99669647780918090292241097)
        ·
          refine ⟨74752235835688567719180823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99669647780918090292241097 74752235835688567719180823)
          ·
            refine ⟨112128353753532851578771235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74752235835688567719180823 112128353753532851578771235)
            ·
              refine ⟨168192530630299277368156853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112128353753532851578771235 168192530630299277368156853)
              ·
                refine ⟨15768049746590557253264705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168192530630299277368156853 15768049746590557253264705)
                ·
                  refine ⟨11826037309942917939948529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15768049746590557253264705 11826037309942917939948529)
                  ·
                    refine ⟨8869527982457188454961397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11826037309942917939948529 8869527982457188454961397)
                    ·
                      refine ⟨831518248355361417652631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8869527982457188454961397 831518248355361417652631)
                      ·
                        rfl

theorem cell23_1619376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_1619376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619376 prefixEnd_1619376 := by exact prefixLift 1619376
  have htrace : WordTrace (prefixWord ++ tailWord_1619376) baseStart_1619376 baseEnd_1619376 := by
    simpa [prefixWord, tailWord_1619376, baseEnd_1619376] using wordTrace_append hprefix tailTrace_1619376
  have hstable : (prefixWord ++ tailWord_1619376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619376).length < 2 ^ (prefixWord ++ tailWord_1619376).sum := by decide
  have hdescent : baseEnd_1619376 < baseStart_1619376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619413 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 2, 6]
def baseStart_1619413 : Nat := 118140960795 + 1619413 * 2 ^ 59
def prefixEnd_1619413 : Nat := 4983230072969 + 3 ^ 40 * 1619413 * 2
def baseEnd_1619413 : Nat := 277179082379859257629987

theorem tailTrace_1619413 : CollatzResearch.WordTrace tailWord_1619413 prefixEnd_1619413 277179082379859257629987 := by
  unfold tailWord_1619413
  simp only [CollatzResearch.WordTrace]
  refine ⟨59064844482150749566350893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39376562988100499710900595 59064844482150749566350893)
  ·
    refine ⟨22149316680806531087381585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59064844482150749566350893 22149316680806531087381585)
    ·
      refine ⟨16611987510604898315536189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22149316680806531087381585 16611987510604898315536189)
      ·
        refine ⟨6229495316476836868326071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16611987510604898315536189 6229495316476836868326071)
        ·
          refine ⟨9344242974715255302489107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6229495316476836868326071 9344242974715255302489107)
          ·
            refine ⟨14016364462072882953733661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9344242974715255302489107 14016364462072882953733661)
            ·
              refine ⟨5256136673277331107650123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14016364462072882953733661 5256136673277331107650123)
              ·
                refine ⟨7884205009915996661475185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5256136673277331107650123 7884205009915996661475185)
                ·
                  refine ⟨5913153757436997496106389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7884205009915996661475185 5913153757436997496106389)
                  ·
                    refine ⟨277179082379859257629987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5913153757436997496106389 277179082379859257629987)
                    ·
                      rfl

theorem cell23_1619413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_1619413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619413 prefixEnd_1619413 := by exact prefixLift 1619413
  have htrace : WordTrace (prefixWord ++ tailWord_1619413) baseStart_1619413 baseEnd_1619413 := by
    simpa [prefixWord, tailWord_1619413, baseEnd_1619413] using wordTrace_append hprefix tailTrace_1619413
  have hstable : (prefixWord ++ tailWord_1619413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619413).length < 2 ^ (prefixWord ++ tailWord_1619413).sum := by decide
  have hdescent : baseEnd_1619413 < baseStart_1619413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619414 : List Nat := [5, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_1619414 : Nat := 118140960795 + 1619414 * 2 ^ 59
def prefixEnd_1619414 : Nat := 4983230072969 + 3 ^ 40 * 1619414 * 2
def baseEnd_1619414 : Nat := 831537760620232268977457

theorem tailTrace_1619414 : CollatzResearch.WordTrace tailWord_1619414 prefixEnd_1619414 831537760620232268977457 := by
  unfold tailWord_1619414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3691555059696695421071081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39376587303431417824758197 3691555059696695421071081)
  ·
    refine ⟨2768666294772521565803311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3691555059696695421071081 2768666294772521565803311)
    ·
      refine ⟨4152999442158782348704967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2768666294772521565803311 4152999442158782348704967)
      ·
        refine ⟨6229499163238173523057451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4152999442158782348704967 6229499163238173523057451)
        ·
          refine ⟨9344248744857260284586177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6229499163238173523057451 9344248744857260284586177)
          ·
            refine ⟨7008186558642945213439633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9344248744857260284586177 7008186558642945213439633)
            ·
              refine ⟨5256139918982208910079725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7008186558642945213439633 5256139918982208910079725)
              ·
                refine ⟨1971052469618328341279897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5256139918982208910079725 1971052469618328341279897)
                ·
                  refine ⟨1478289352213746255959923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1971052469618328341279897 1478289352213746255959923)
                  ·
                    refine ⟨2217434028320619383939885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1478289352213746255959923 2217434028320619383939885)
                    ·
                      refine ⟨831537760620232268977457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2217434028320619383939885 831537760620232268977457)
                      ·
                        rfl

theorem cell23_1619414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_1619414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619414 prefixEnd_1619414 := by exact prefixLift 1619414
  have htrace : WordTrace (prefixWord ++ tailWord_1619414) baseStart_1619414 baseEnd_1619414 := by
    simpa [prefixWord, tailWord_1619414, baseEnd_1619414] using wordTrace_append hprefix tailTrace_1619414
  have hstable : (prefixWord ++ tailWord_1619414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619414).length < 2 ^ (prefixWord ++ tailWord_1619414).sum := by decide
  have hdescent : baseEnd_1619414 < baseStart_1619414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619423 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 3]
def baseStart_1619423 : Nat := 118140960795 + 1619423 * 2 ^ 59
def prefixEnd_1619423 : Nat := 4983230072969 + 3 ^ 40 * 1619423 * 2
def baseEnd_1619423 : Nat := 831542381946122733764915

theorem tailTrace_1619423 : CollatzResearch.WordTrace tailWord_1619423 prefixEnd_1619423 831542381946122733764915 := by
  unfold tailWord_1619423
  simp only [CollatzResearch.WordTrace]
  refine ⟨59065209212114521274214923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39376806141409680849476615 59065209212114521274214923)
  ·
    refine ⟨88597813818171781911322385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59065209212114521274214923 88597813818171781911322385)
    ·
      refine ⟨66448360363628836433491789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88597813818171781911322385 66448360363628836433491789)
      ·
        refine ⟨24918135136360813662559421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66448360363628836433491789 24918135136360813662559421)
        ·
          refine ⟨9344300676135305123459783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24918135136360813662559421 9344300676135305123459783)
          ·
            refine ⟨14016451014202957685189675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9344300676135305123459783 14016451014202957685189675)
            ·
              refine ⟨21024676521304436527784513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14016451014202957685189675 21024676521304436527784513)
              ·
                refine ⟨15768507390978327395838385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21024676521304436527784513 15768507390978327395838385)
                ·
                  refine ⟨11826380543233745546878789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15768507390978327395838385 11826380543233745546878789)
                  ·
                    refine ⟨2217446351856327290039773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11826380543233745546878789 2217446351856327290039773)
                    ·
                      refine ⟨831542381946122733764915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2217446351856327290039773 831542381946122733764915)
                      ·
                        rfl

theorem cell23_1619423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_1619423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619423 prefixEnd_1619423 := by exact prefixLift 1619423
  have htrace : WordTrace (prefixWord ++ tailWord_1619423) baseStart_1619423 baseEnd_1619423 := by
    simpa [prefixWord, tailWord_1619423, baseEnd_1619423] using wordTrace_append hprefix tailTrace_1619423
  have hstable : (prefixWord ++ tailWord_1619423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619423).length < 2 ^ (prefixWord ++ tailWord_1619423).sum := by decide
  have hdescent : baseEnd_1619423 < baseStart_1619423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619530 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 4, 2, 3]
def baseStart_1619530 : Nat := 118140960795 + 1619530 * 2 ^ 59
def prefixEnd_1619530 : Nat := 4983230072969 + 3 ^ 40 * 1619530 * 2
def baseEnd_1619530 : Nat := 831597324376153815126923

theorem tailTrace_1619530 : CollatzResearch.WordTrace tailWord_1619530 prefixEnd_1619530 831597324376153815126923 := by
  unfold tailWord_1619530
  simp only [CollatzResearch.WordTrace]
  refine ⟨14767277955681719637090011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39379407881817919032240029 14767277955681719637090011)
  ·
    refine ⟨22150916933522579455635017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14767277955681719637090011 22150916933522579455635017)
    ·
      refine ⟨16613187700141934591726263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22150916933522579455635017 16613187700141934591726263)
      ·
        refine ⟨24919781550212901887589395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16613187700141934591726263 24919781550212901887589395)
        ·
          refine ⟨37379672325319352831384093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24919781550212901887589395 37379672325319352831384093)
          ·
            refine ⟨14017377121994757311769035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37379672325319352831384093 14017377121994757311769035)
            ·
              refine ⟨21026065682992135967653553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14017377121994757311769035 21026065682992135967653553)
              ·
                refine ⟨15769549262244101975740165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21026065682992135967653553 15769549262244101975740165)
                ·
                  refine ⟨2956790486670769120451281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15769549262244101975740165 2956790486670769120451281)
                  ·
                    refine ⟨2217592865003076840338461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2956790486670769120451281 2217592865003076840338461)
                    ·
                      refine ⟨831597324376153815126923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2217592865003076840338461 831597324376153815126923)
                      ·
                        rfl

theorem cell23_1619530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_1619530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619530 prefixEnd_1619530 := by exact prefixLift 1619530
  have htrace : WordTrace (prefixWord ++ tailWord_1619530) baseStart_1619530 baseEnd_1619530 := by
    simpa [prefixWord, tailWord_1619530, baseEnd_1619530] using wordTrace_append hprefix tailTrace_1619530
  have hstable : (prefixWord ++ tailWord_1619530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619530).length < 2 ^ (prefixWord ++ tailWord_1619530).sum := by decide
  have hdescent : baseEnd_1619530 < baseStart_1619530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619577 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 3, 1, 3]
def baseStart_1619577 : Nat := 118140960795 + 1619577 * 2 ^ 59
def prefixEnd_1619577 : Nat := 4983230072969 + 3 ^ 40 * 1619577 * 2
def baseEnd_1619577 : Nat := 831621457966915131239207

theorem tailTrace_1619577 : CollatzResearch.WordTrace tailWord_1619577 prefixEnd_1619577 831621457966915131239207 := by
  unfold tailWord_1619577
  simp only [CollatzResearch.WordTrace]
  refine ⟨59070826053556605575320985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39380550702371070383547323 59070826053556605575320985)
  ·
    refine ⟨44303119540167454181490739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59070826053556605575320985 44303119540167454181490739)
    ·
      refine ⟨66454679310251181272236109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44303119540167454181490739 66454679310251181272236109)
      ·
        refine ⟨24920504741344192977088541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66454679310251181272236109 24920504741344192977088541)
        ·
          refine ⟨9345189278004072366408203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24920504741344192977088541 9345189278004072366408203)
          ·
            refine ⟨14017783917006108549612305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9345189278004072366408203 14017783917006108549612305)
            ·
              refine ⟨10513337937754581412209229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14017783917006108549612305 10513337937754581412209229)
              ·
                refine ⟨3942501726657968029578461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10513337937754581412209229 3942501726657968029578461)
                ·
                  refine ⟨1478438147496738011091923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3942501726657968029578461 1478438147496738011091923)
                  ·
                    refine ⟨2217657221245107016637885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1478438147496738011091923 2217657221245107016637885)
                    ·
                      refine ⟨831621457966915131239207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2217657221245107016637885 831621457966915131239207)
                      ·
                        rfl

theorem cell23_1619577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_1619577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619577 prefixEnd_1619577 := by exact prefixLift 1619577
  have htrace : WordTrace (prefixWord ++ tailWord_1619577) baseStart_1619577 baseEnd_1619577 := by
    simpa [prefixWord, tailWord_1619577, baseEnd_1619577] using wordTrace_append hprefix tailTrace_1619577
  have hstable : (prefixWord ++ tailWord_1619577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619577).length < 2 ^ (prefixWord ++ tailWord_1619577).sum := by decide
  have hdescent : baseEnd_1619577 < baseStart_1619577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619594 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 3, 1, 3]
def baseStart_1619594 : Nat := 118140960795 + 1619594 * 2 ^ 59
def prefixEnd_1619594 : Nat := 4983230072969 + 3 ^ 40 * 1619594 * 2
def baseEnd_1619594 : Nat := 831630187138041564726629

theorem tailTrace_1619594 : CollatzResearch.WordTrace tailWord_1619594 prefixEnd_1619594 831630187138041564726629 := by
  unfold tailWord_1619594
  simp only [CollatzResearch.WordTrace]
  refine ⟨14767861523623754369672459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39380964062996678319126557 14767861523623754369672459)
  ·
    refine ⟨22151792285435631554508689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14767861523623754369672459 22151792285435631554508689)
    ·
      refine ⟨16613844214076723665881517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22151792285435631554508689 16613844214076723665881517)
      ·
        refine ⟨6230191580278771374705569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16613844214076723665881517 6230191580278771374705569)
        ·
          refine ⟨4672643685209078531029177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6230191580278771374705569 4672643685209078531029177)
          ·
            refine ⟨3504482763906808898271883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4672643685209078531029177 3504482763906808898271883)
            ·
              refine ⟨5256724145860213347407825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3504482763906808898271883 5256724145860213347407825)
              ·
                refine ⟨3942543109395160010555869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5256724145860213347407825 3942543109395160010555869)
                ·
                  refine ⟨1478453666023185003958451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3942543109395160010555869 1478453666023185003958451)
                  ·
                    refine ⟨2217680499034777505937677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1478453666023185003958451 2217680499034777505937677)
                    ·
                      refine ⟨831630187138041564726629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2217680499034777505937677 831630187138041564726629)
                      ·
                        rfl

theorem cell23_1619594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_1619594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619594 prefixEnd_1619594 := by exact prefixLift 1619594
  have htrace : WordTrace (prefixWord ++ tailWord_1619594) baseStart_1619594 baseEnd_1619594 := by
    simpa [prefixWord, tailWord_1619594, baseEnd_1619594] using wordTrace_append hprefix tailTrace_1619594
  have hstable : (prefixWord ++ tailWord_1619594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619594).length < 2 ^ (prefixWord ++ tailWord_1619594).sum := by decide
  have hdescent : baseEnd_1619594 < baseStart_1619594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619603 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 5]
def baseStart_1619603 : Nat := 118140960795 + 1619603 * 2 ^ 59
def prefixEnd_1619603 : Nat := 4983230072969 + 3 ^ 40 * 1619603 * 2
def baseEnd_1619603 : Nat := 831634808463932029514087

theorem tailTrace_1619603 : CollatzResearch.WordTrace tailWord_1619603 prefixEnd_1619603 831634808463932029514087 := by
  unfold tailWord_1619603
  simp only [CollatzResearch.WordTrace]
  refine ⟨59071774351462412015767463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39381182900974941343844975 59071774351462412015767463)
  ·
    refine ⟨88607661527193618023651195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59071774351462412015767463 88607661527193618023651195)
    ·
      refine ⟨132911492290790427035476793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88607661527193618023651195 132911492290790427035476793)
      ·
        refine ⟨99683619218092820276607595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132911492290790427035476793 99683619218092820276607595)
        ·
          refine ⟨149525428827139230414911393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99683619218092820276607595 149525428827139230414911393)
          ·
            refine ⟨112144071620354422811183545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149525428827139230414911393 112144071620354422811183545)
            ·
              refine ⟨84108053715265817108387659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112144071620354422811183545 84108053715265817108387659)
              ·
                refine ⟨126162080572898725662581489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84108053715265817108387659 126162080572898725662581489)
                ·
                  refine ⟨94621560429674044246936117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126162080572898725662581489 94621560429674044246936117)
                  ·
                    refine ⟨8870771290281941648150261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94621560429674044246936117 8870771290281941648150261)
                    ·
                      refine ⟨831634808463932029514087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8870771290281941648150261 831634808463932029514087)
                      ·
                        rfl

theorem cell23_1619603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_1619603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619603 prefixEnd_1619603 := by exact prefixLift 1619603
  have htrace : WordTrace (prefixWord ++ tailWord_1619603) baseStart_1619603 baseEnd_1619603 := by
    simpa [prefixWord, tailWord_1619603, baseEnd_1619603] using wordTrace_append hprefix tailTrace_1619603
  have hstable : (prefixWord ++ tailWord_1619603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619603).length < 2 ^ (prefixWord ++ tailWord_1619603).sum := by decide
  have hdescent : baseEnd_1619603 < baseStart_1619603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619614 : List Nat := [4, 3, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_1619614 : Nat := 118140960795 + 1619614 * 2 ^ 59
def prefixEnd_1619614 : Nat := 4983230072969 + 3 ^ 40 * 1619614 * 2
def baseEnd_1619614 : Nat := 277213485583710495492179

theorem tailTrace_1619614 : CollatzResearch.WordTrace tailWord_1619614 prefixEnd_1619614 277213485583710495492179 := by
  unfold tailWord_1619614
  simp only [CollatzResearch.WordTrace]
  refine ⟨7384021944302820111802237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39381450369615040596278597 7384021944302820111802237)
  ·
    refine ⟨2769008229113557541925839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7384021944302820111802237 2769008229113557541925839)
    ·
      refine ⟨4153512343670336312888759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2769008229113557541925839 4153512343670336312888759)
      ·
        refine ⟨6230268515505504469333139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4153512343670336312888759 6230268515505504469333139)
        ·
          refine ⟨9345402773258256703999709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6230268515505504469333139 9345402773258256703999709)
          ·
            refine ⟨3504526039971846263999891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9345402773258256703999709 3504526039971846263999891)
            ·
              refine ⟨5256789059957769395999837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3504526039971846263999891 5256789059957769395999837)
              ·
                refine ⟨1971295897484163523499939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5256789059957769395999837 1971295897484163523499939)
                ·
                  refine ⟨2956943846226245285249909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1971295897484163523499939 2956943846226245285249909)
                  ·
                    refine ⟨277213485583710495492179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2956943846226245285249909 277213485583710495492179)
                    ·
                      rfl

theorem cell23_1619614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_1619614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619614 prefixEnd_1619614 := by exact prefixLift 1619614
  have htrace : WordTrace (prefixWord ++ tailWord_1619614) baseStart_1619614 baseEnd_1619614 := by
    simpa [prefixWord, tailWord_1619614, baseEnd_1619614] using wordTrace_append hprefix tailTrace_1619614
  have hstable : (prefixWord ++ tailWord_1619614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619614).length < 2 ^ (prefixWord ++ tailWord_1619614).sum := by decide
  have hdescent : baseEnd_1619614 < baseStart_1619614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619634 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2]
def baseStart_1619634 : Nat := 118140960795 + 1619634 * 2 ^ 59
def prefixEnd_1619634 : Nat := 4983230072969 + 3 ^ 40 * 1619634 * 2
def baseEnd_1619634 : Nat := 831650726364221408226445

theorem tailTrace_1619634 : CollatzResearch.WordTrace tailWord_1619634 prefixEnd_1619634 831650726364221408226445 := by
  unfold tailWord_1619634
  simp only [CollatzResearch.WordTrace]
  refine ⟨14768226253587526077536489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39381936676233402873430637 14768226253587526077536489)
  ·
    refine ⟨11076169690190644558152367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14768226253587526077536489 11076169690190644558152367)
    ·
      refine ⟨16614254535285966837228551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11076169690190644558152367 16614254535285966837228551)
      ·
        refine ⟨24921381802928950255842827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16614254535285966837228551 24921381802928950255842827)
        ·
          refine ⟨37382072704393425383764241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24921381802928950255842827 37382072704393425383764241)
          ·
            refine ⟨28036554528295069037823181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37382072704393425383764241 28036554528295069037823181)
            ·
              refine ⟨10513707948110650889183693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28036554528295069037823181 10513707948110650889183693)
              ·
                refine ⟨3942640480541494083443885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10513707948110650889183693 3942640480541494083443885)
                ·
                  refine ⟨1478490180203060281291457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3942640480541494083443885 1478490180203060281291457)
                  ·
                    refine ⟨1108867635152295210968593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1478490180203060281291457 1108867635152295210968593)
                    ·
                      refine ⟨831650726364221408226445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1108867635152295210968593 831650726364221408226445)
                      ·
                        rfl

theorem cell23_1619634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_1619634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619634 prefixEnd_1619634 := by exact prefixLift 1619634
  have htrace : WordTrace (prefixWord ++ tailWord_1619634) baseStart_1619634 baseEnd_1619634 := by
    simpa [prefixWord, tailWord_1619634, baseEnd_1619634] using wordTrace_append hprefix tailTrace_1619634
  have hstable : (prefixWord ++ tailWord_1619634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619634).length < 2 ^ (prefixWord ++ tailWord_1619634).sum := by decide
  have hdescent : baseEnd_1619634 < baseStart_1619634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619684 : List Nat := [2, 3, 1, 1, 1, 3, 2, 4, 2, 1, 3]
def baseStart_1619684 : Nat := 118140960795 + 1619684 * 2 ^ 59
def prefixEnd_1619684 : Nat := 4983230072969 + 3 ^ 40 * 1619684 * 2
def baseEnd_1619684 : Nat := 831676400396946212601215

theorem tailTrace_1619684 : CollatzResearch.WordTrace tailWord_1619684 prefixEnd_1619684 831676400396946212601215 := by
  unfold tailWord_1619684
  simp only [CollatzResearch.WordTrace]
  refine ⟨29537364332084481424733053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39383152442779308566310737 29537364332084481424733053)
  ·
    refine ⟨11076511624531680534274895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29537364332084481424733053 11076511624531680534274895)
    ·
      refine ⟨16614767436797520801412343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11076511624531680534274895 16614767436797520801412343)
      ·
        refine ⟨24922151155196281202118515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16614767436797520801412343 24922151155196281202118515)
        ·
          refine ⟨37383226732794421803177773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24922151155196281202118515 37383226732794421803177773)
          ·
            refine ⟨14018710024797908176191665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37383226732794421803177773 14018710024797908176191665)
            ·
              refine ⟨10514032518598431132143749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14018710024797908176191665 10514032518598431132143749)
              ·
                refine ⟨1971381097237205837276953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10514032518598431132143749 1971381097237205837276953)
                ·
                  refine ⟨1478535822927904377957715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1971381097237205837276953 1478535822927904377957715)
                  ·
                    refine ⟨2217803734391856566936573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1478535822927904377957715 2217803734391856566936573)
                    ·
                      refine ⟨831676400396946212601215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2217803734391856566936573 831676400396946212601215)
                      ·
                        rfl

theorem cell23_1619684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_1619684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619684 prefixEnd_1619684 := by exact prefixLift 1619684
  have htrace : WordTrace (prefixWord ++ tailWord_1619684) baseStart_1619684 baseEnd_1619684 := by
    simpa [prefixWord, tailWord_1619684, baseEnd_1619684] using wordTrace_append hprefix tailTrace_1619684
  have hstable : (prefixWord ++ tailWord_1619684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619684).length < 2 ^ (prefixWord ++ tailWord_1619684).sum := by decide
  have hdescent : baseEnd_1619684 < baseStart_1619684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619694 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 3, 3, 2]
def baseStart_1619694 : Nat := 118140960795 + 1619694 * 2 ^ 59
def prefixEnd_1619694 : Nat := 4983230072969 + 3 ^ 40 * 1619694 * 2
def baseEnd_1619694 : Nat := 831681535203491173476169

theorem tailTrace_1619694 : CollatzResearch.WordTrace tailWord_1619694 prefixEnd_1619694 831681535203491173476169 := by
  unfold tailWord_1619694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7384386674266591819666267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39383395596088489704886757 7384386674266591819666267)
  ·
    refine ⟨11076580011399887729499401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7384386674266591819666267 11076580011399887729499401)
    ·
      refine ⟨8307435008549915797124551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11076580011399887729499401 8307435008549915797124551)
      ·
        refine ⟨12461152512824873695686827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8307435008549915797124551 12461152512824873695686827)
        ·
          refine ⟨18691728769237310543530241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12461152512824873695686827 18691728769237310543530241)
          ·
            refine ⟨14018796576927982907647681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18691728769237310543530241 14018796576927982907647681)
            ·
              refine ⟨10514097432695987180735761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14018796576927982907647681 10514097432695987180735761)
              ·
                refine ⟨7885573074521990385551821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10514097432695987180735761 7885573074521990385551821)
                ·
                  refine ⟨2957089902945746394581933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7885573074521990385551821 2957089902945746394581933)
                  ·
                    refine ⟨1108908713604654897968225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2957089902945746394581933 1108908713604654897968225)
                    ·
                      refine ⟨831681535203491173476169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1108908713604654897968225 831681535203491173476169)
                      ·
                        rfl

theorem cell23_1619694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_1619694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619694 prefixEnd_1619694 := by exact prefixLift 1619694
  have htrace : WordTrace (prefixWord ++ tailWord_1619694) baseStart_1619694 baseEnd_1619694 := by
    simpa [prefixWord, tailWord_1619694, baseEnd_1619694] using wordTrace_append hprefix tailTrace_1619694
  have hstable : (prefixWord ++ tailWord_1619694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619694).length < 2 ^ (prefixWord ++ tailWord_1619694).sum := by decide
  have hdescent : baseEnd_1619694 < baseStart_1619694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619724 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 6, 2, 2]
def baseStart_1619724 : Nat := 118140960795 + 1619724 * 2 ^ 59
def prefixEnd_1619724 : Nat := 4983230072969 + 3 ^ 40 * 1619724 * 2
def baseEnd_1619724 : Nat := 831696939623126056101031

theorem tailTrace_1619724 : CollatzResearch.WordTrace tailWord_1619724 prefixEnd_1619724 831696939623126056101031 := by
  unfold tailWord_1619724
  simp only [CollatzResearch.WordTrace]
  refine ⟨29538093792012024840461113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39384125056016033120614817 29538093792012024840461113)
  ·
    refine ⟨22153570344009018630345835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29538093792012024840461113 22153570344009018630345835)
    ·
      refine ⟨33230355516013527945518753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22153570344009018630345835 33230355516013527945518753)
      ·
        refine ⟨24922766637010145959139065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33230355516013527945518753 24922766637010145959139065)
        ·
          refine ⟨18692074977757609469354299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24922766637010145959139065 18692074977757609469354299)
          ·
            refine ⟨28038112466636414204031449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18692074977757609469354299 28038112466636414204031449)
            ·
              refine ⟨21028584349977310653023587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28038112466636414204031449 21028584349977310653023587)
              ·
                refine ⟨31542876524965965979535381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21028584349977310653023587 31542876524965965979535381)
                ·
                  refine ⟨1478572337107779655290721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31542876524965965979535381 1478572337107779655290721)
                  ·
                    refine ⟨1108929252830834741468041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1478572337107779655290721 1108929252830834741468041)
                    ·
                      refine ⟨831696939623126056101031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1108929252830834741468041 831696939623126056101031)
                      ·
                        rfl

theorem cell23_1619724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_1619724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619724 prefixEnd_1619724 := by exact prefixLift 1619724
  have htrace : WordTrace (prefixWord ++ tailWord_1619724) baseStart_1619724 baseEnd_1619724 := by
    simpa [prefixWord, tailWord_1619724, baseEnd_1619724] using wordTrace_append hprefix tailTrace_1619724
  have hstable : (prefixWord ++ tailWord_1619724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619724).length < 2 ^ (prefixWord ++ tailWord_1619724).sum := by decide
  have hdescent : baseEnd_1619724 < baseStart_1619724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619758 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_1619758 : Nat := 118140960795 + 1619758 * 2 ^ 59
def prefixEnd_1619758 : Nat := 4983230072969 + 3 ^ 40 * 1619758 * 2
def baseEnd_1619758 : Nat := 831714397965378923075875

theorem tailTrace_1619758 : CollatzResearch.WordTrace tailWord_1619758 prefixEnd_1619758 831714397965378923075875 := by
  unfold tailWord_1619758
  simp only [CollatzResearch.WordTrace]
  refine ⟨7384678458237609185957491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39384951777267248991773285 7384678458237609185957491)
  ·
    refine ⟨11077017687356413778936237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7384678458237609185957491 11077017687356413778936237)
    ·
      refine ⟨4153881632758655167101089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11077017687356413778936237 4153881632758655167101089)
      ·
        refine ⟨3115411224568991375325817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4153881632758655167101089 3115411224568991375325817)
        ·
          refine ⟨2336558418426743531494363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3115411224568991375325817 2336558418426743531494363)
          ·
            refine ⟨3504837627640115297241545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336558418426743531494363 3504837627640115297241545)
            ·
              refine ⟨2628628220730086472931159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3504837627640115297241545 2628628220730086472931159)
              ·
                refine ⟨3942942331095129709396739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2628628220730086472931159 3942942331095129709396739)
                ·
                  refine ⟨5914413496642694564095109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3942942331095129709396739 5914413496642694564095109)
                  ·
                    refine ⟨1108952530620505230767833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5914413496642694564095109 1108952530620505230767833)
                    ·
                      refine ⟨831714397965378923075875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1108952530620505230767833 831714397965378923075875)
                      ·
                        rfl

theorem cell23_1619758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_1619758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619758 prefixEnd_1619758 := by exact prefixLift 1619758
  have htrace : WordTrace (prefixWord ++ tailWord_1619758) baseStart_1619758 baseEnd_1619758 := by
    simpa [prefixWord, tailWord_1619758, baseEnd_1619758] using wordTrace_append hprefix tailTrace_1619758
  have hstable : (prefixWord ++ tailWord_1619758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619758).length < 2 ^ (prefixWord ++ tailWord_1619758).sum := by decide
  have hdescent : baseEnd_1619758 < baseStart_1619758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619764 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 7]
def baseStart_1619764 : Nat := 118140960795 + 1619764 * 2 ^ 59
def prefixEnd_1619764 : Nat := 4983230072969 + 3 ^ 40 * 1619764 * 2
def baseEnd_1619764 : Nat := 92413053205478433288983

theorem tailTrace_1619764 : CollatzResearch.WordTrace tailWord_1619764 prefixEnd_1619764 92413053205478433288983 := by
  unfold tailWord_1619764
  simp only [CollatzResearch.WordTrace]
  refine ⟨29538823251939568256189173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39385097669252757674918897 29538823251939568256189173)
  ·
    refine ⟨2769264679869334524017735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29538823251939568256189173 2769264679869334524017735)
    ·
      refine ⟨4153897019804001786026603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2769264679869334524017735 4153897019804001786026603)
      ·
        refine ⟨6230845529706002679039905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4153897019804001786026603 6230845529706002679039905)
        ·
          refine ⟨4673134147279502009279929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6230845529706002679039905 4673134147279502009279929)
          ·
            refine ⟨3504850610459626506959947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4673134147279502009279929 3504850610459626506959947)
            ·
              refine ⟨5257275915689439760439921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3504850610459626506959947 5257275915689439760439921)
              ·
                refine ⟨3942956936767079820329941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5257275915689439760439921 3942956936767079820329941)
                ·
                  refine ⟨92413053205478433288983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3942956936767079820329941 92413053205478433288983)
                  ·
                    rfl

theorem cell23_1619764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_1619764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619764 prefixEnd_1619764 := by exact prefixLift 1619764
  have htrace : WordTrace (prefixWord ++ tailWord_1619764) baseStart_1619764 baseEnd_1619764 := by
    simpa [prefixWord, tailWord_1619764, baseEnd_1619764] using wordTrace_append hprefix tailTrace_1619764
  have hstable : (prefixWord ++ tailWord_1619764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619764).length < 2 ^ (prefixWord ++ tailWord_1619764).sum := by decide
  have hdescent : baseEnd_1619764 < baseStart_1619764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619858 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 3, 4]
def baseStart_1619858 : Nat := 118140960795 + 1619858 * 2 ^ 59
def prefixEnd_1619858 : Nat := 4983230072969 + 3 ^ 40 * 1619858 * 2
def baseEnd_1619858 : Nat := 277255248676942843941805

theorem tailTrace_1619858 : CollatzResearch.WordTrace tailWord_1619858 prefixEnd_1619858 277255248676942843941805 := by
  unfold tailWord_1619858
  simp only [CollatzResearch.WordTrace]
  refine ⟨14770268741384647641575057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39387383310359060377533485 14770268741384647641575057)
  ·
    refine ⟨11077701556038485731181293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14770268741384647641575057 11077701556038485731181293)
    ·
      refine ⟨4154138083514432149192985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11077701556038485731181293 4154138083514432149192985)
      ·
        refine ⟨3115603562635824111894739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4154138083514432149192985 3115603562635824111894739)
        ·
          refine ⟨4673405343953736167842109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3115603562635824111894739 4673405343953736167842109)
          ·
            refine ⟨1752527003982651062940791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4673405343953736167842109 1752527003982651062940791)
            ·
              refine ⟨2628790505973976594411187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1752527003982651062940791 2628790505973976594411187)
              ·
                refine ⟨3943185758960964891616781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2628790505973976594411187 3943185758960964891616781)
                ·
                  refine ⟨1478694659610361834356293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3943185758960964891616781 1478694659610361834356293)
                  ·
                    refine ⟨277255248676942843941805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1478694659610361834356293 277255248676942843941805)
                    ·
                      rfl

theorem cell23_1619858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_1619858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619858 prefixEnd_1619858 := by exact prefixLift 1619858
  have htrace : WordTrace (prefixWord ++ tailWord_1619858) baseStart_1619858 baseEnd_1619858 := by
    simpa [prefixWord, tailWord_1619858, baseEnd_1619858] using wordTrace_append hprefix tailTrace_1619858
  have hstable : (prefixWord ++ tailWord_1619858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619858).length < 2 ^ (prefixWord ++ tailWord_1619858).sum := by decide
  have hdescent : baseEnd_1619858 < baseStart_1619858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619891 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 2, 3, 2]
def baseStart_1619891 : Nat := 118140960795 + 1619891 * 2 ^ 59
def prefixEnd_1619891 : Nat := 4983230072969 + 3 ^ 40 * 1619891 * 2
def baseEnd_1619891 : Nat := 831782690892426902712763

theorem tailTrace_1619891 : CollatzResearch.WordTrace tailWord_1619891 prefixEnd_1619891 831782690892426902712763 := by
  unfold tailWord_1619891
  simp only [CollatzResearch.WordTrace]
  refine ⟨59082278574419037202251527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39388185716279358134834351 59082278574419037202251527)
  ·
    refine ⟨88623417861628555803377291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59082278574419037202251527 88623417861628555803377291)
    ·
      refine ⟨132935126792442833705065937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88623417861628555803377291 132935126792442833705065937)
      ·
        refine ⟨99701345094332125278799453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132935126792442833705065937 99701345094332125278799453)
        ·
          refine ⟨37388004410374546979549795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99701345094332125278799453 37388004410374546979549795)
          ·
            refine ⟨56082006615561820469324693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37388004410374546979549795 56082006615561820469324693)
            ·
              refine ⟨2628844060104460334499595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56082006615561820469324693 2628844060104460334499595)
              ·
                refine ⟨3943266090156690501749393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2628844060104460334499595 3943266090156690501749393)
                ·
                  refine ⟨2957449567617517876312045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3943266090156690501749393 2957449567617517876312045)
                  ·
                    refine ⟨1109043587856569203617017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2957449567617517876312045 1109043587856569203617017)
                    ·
                      refine ⟨831782690892426902712763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1109043587856569203617017 831782690892426902712763)
                      ·
                        rfl

theorem cell23_1619891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 3, 2].length) (baseStart_1619891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619891 prefixEnd_1619891 := by exact prefixLift 1619891
  have htrace : WordTrace (prefixWord ++ tailWord_1619891) baseStart_1619891 baseEnd_1619891 := by
    simpa [prefixWord, tailWord_1619891, baseEnd_1619891] using wordTrace_append hprefix tailTrace_1619891
  have hstable : (prefixWord ++ tailWord_1619891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619891).length < 2 ^ (prefixWord ++ tailWord_1619891).sum := by decide
  have hdescent : baseEnd_1619891 < baseStart_1619891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619914 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 4, 4]
def baseStart_1619914 : Nat := 118140960795 + 1619914 * 2 ^ 59
def prefixEnd_1619914 : Nat := 4983230072969 + 3 ^ 40 * 1619914 * 2
def baseEnd_1619914 : Nat := 277264833649160104241719

theorem tailTrace_1619914 : CollatzResearch.WordTrace tailWord_1619914 prefixEnd_1619914 277264833649160104241719 := by
  unfold tailWord_1619914
  simp only [CollatzResearch.WordTrace]
  refine ⟨14770779363333928032584699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39388744968890474753559197 14770779363333928032584699)
  ·
    refine ⟨22156169045000892048877049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14770779363333928032584699 22156169045000892048877049)
    ·
      refine ⟨16617126783750669036657787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22156169045000892048877049 16617126783750669036657787)
      ·
        refine ⟨24925690175626003554986681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16617126783750669036657787 24925690175626003554986681)
        ·
          refine ⟨18694267631719502666240011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24925690175626003554986681 18694267631719502666240011)
          ·
            refine ⟨28041401447579253999360017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18694267631719502666240011 28041401447579253999360017)
            ·
              refine ⟨21031051085684440499520013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28041401447579253999360017 21031051085684440499520013)
              ·
                refine ⟨7886644157131665187320005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21031051085684440499520013 7886644157131665187320005)
                ·
                  refine ⟨1478745779462187222622501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7886644157131665187320005 1478745779462187222622501)
                  ·
                    refine ⟨277264833649160104241719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1478745779462187222622501 277264833649160104241719)
                    ·
                      rfl

theorem cell23_1619914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_1619914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619914 prefixEnd_1619914 := by exact prefixLift 1619914
  have htrace : WordTrace (prefixWord ++ tailWord_1619914) baseStart_1619914 baseEnd_1619914 := by
    simpa [prefixWord, tailWord_1619914, baseEnd_1619914] using wordTrace_append hprefix tailTrace_1619914
  have hstable : (prefixWord ++ tailWord_1619914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619914).length < 2 ^ (prefixWord ++ tailWord_1619914).sum := by decide
  have hdescent : baseEnd_1619914 < baseStart_1619914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619924 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1619924 : Nat := 118140960795 + 1619924 * 2 ^ 59
def prefixEnd_1619924 : Nat := 4983230072969 + 3 ^ 40 * 1619924 * 2
def baseEnd_1619924 : Nat := 831799635754025273600111

theorem tailTrace_1619924 : CollatzResearch.WordTrace tailWord_1619924 prefixEnd_1619924 831799635754025273600111 := by
  unfold tailWord_1619924
  simp only [CollatzResearch.WordTrace]
  refine ⟨29541741091649741919101413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39388988122199655892135217 29541741091649741919101413)
  ·
    refine ⟨5539076454684326609831515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29541741091649741919101413 5539076454684326609831515)
    ·
      refine ⟨8308614682026489914747273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5539076454684326609831515 8308614682026489914747273)
      ·
        refine ⟨6231461011519867436060455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8308614682026489914747273 6231461011519867436060455)
        ·
          refine ⟨9347191517279801154090683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6231461011519867436060455 9347191517279801154090683)
          ·
            refine ⟨14020787275919701731136025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9347191517279801154090683 14020787275919701731136025)
            ·
              refine ⟨10515590456939776298352019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14020787275919701731136025 10515590456939776298352019)
              ·
                refine ⟨15773385685409664447528029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10515590456939776298352019 15773385685409664447528029)
                ·
                  refine ⟨5915019632028624167823011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15773385685409664447528029 5915019632028624167823011)
                  ·
                    refine ⟨8872529448042936251734517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5915019632028624167823011 8872529448042936251734517)
                    ·
                      refine ⟨831799635754025273600111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8872529448042936251734517 831799635754025273600111)
                      ·
                        rfl

theorem cell23_1619924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1619924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619924 prefixEnd_1619924 := by exact prefixLift 1619924
  have htrace : WordTrace (prefixWord ++ tailWord_1619924) baseStart_1619924 baseEnd_1619924 := by
    simpa [prefixWord, tailWord_1619924, baseEnd_1619924] using wordTrace_append hprefix tailTrace_1619924
  have hstable : (prefixWord ++ tailWord_1619924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619924).length < 2 ^ (prefixWord ++ tailWord_1619924).sum := by decide
  have hdescent : baseEnd_1619924 < baseStart_1619924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619932 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1619932 : Nat := 118140960795 + 1619932 * 2 ^ 59
def prefixEnd_1619932 : Nat := 4983230072969 + 3 ^ 40 * 1619932 * 2
def baseEnd_1619932 : Nat := 831803743599261242300075

theorem tailTrace_1619932 : CollatzResearch.WordTrace tailWord_1619932 prefixEnd_1619932 831803743599261242300075 := by
  unfold tailWord_1619932
  simp only [CollatzResearch.WordTrace]
  refine ⟨29541886983635250602247025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39389182644847000802996033 29541886983635250602247025)
  ·
    refine ⟨22156415237726437951685269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29541886983635250602247025 22156415237726437951685269)
    ·
      refine ⟨1038581964268426778985247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22156415237726437951685269 1038581964268426778985247)
      ·
        refine ⟨1557872946402640168477871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1038581964268426778985247 1557872946402640168477871)
        ·
          refine ⟨2336809419603960252716807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1557872946402640168477871 2336809419603960252716807)
          ·
            refine ⟨3505214129405940379075211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336809419603960252716807 3505214129405940379075211)
            ·
              refine ⟨5257821194108910568612817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3505214129405940379075211 5257821194108910568612817)
              ·
                refine ⟨3943365895581682926459613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5257821194108910568612817 3943365895581682926459613)
                ·
                  refine ⟨1478762210843131097422355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3943365895581682926459613 1478762210843131097422355)
                  ·
                    refine ⟨2218143316264696646133533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1478762210843131097422355 2218143316264696646133533)
                    ·
                      refine ⟨831803743599261242300075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2218143316264696646133533 831803743599261242300075)
                      ·
                        rfl

theorem cell23_1619932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1619932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619932 prefixEnd_1619932 := by exact prefixLift 1619932
  have htrace : WordTrace (prefixWord ++ tailWord_1619932) baseStart_1619932 baseEnd_1619932 := by
    simpa [prefixWord, tailWord_1619932, baseEnd_1619932] using wordTrace_append hprefix tailTrace_1619932
  have hstable : (prefixWord ++ tailWord_1619932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619932).length < 2 ^ (prefixWord ++ tailWord_1619932).sum := by decide
  have hdescent : baseEnd_1619932 < baseStart_1619932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619972 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 3, 2, 2]
def baseStart_1619972 : Nat := 118140960795 + 1619972 * 2 ^ 59
def prefixEnd_1619972 : Nat := 4983230072969 + 3 ^ 40 * 1619972 * 2
def baseEnd_1619972 : Nat := 831824282825441085799891

theorem tailTrace_1619972 : CollatzResearch.WordTrace tailWord_1619972 prefixEnd_1619972 831824282825441085799891 := by
  unfold tailWord_1619972
  simp only [CollatzResearch.WordTrace]
  refine ⟨29542616443562794017975085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39390155258083725357300113 29542616443562794017975085)
  ·
    refine ⟨11078481166336047756740657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29542616443562794017975085 11078481166336047756740657)
    ·
      refine ⟨8308860874752035817555493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11078481166336047756740657 8308860874752035817555493)
      ·
        refine ⟨1557911414016006715791655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8308860874752035817555493 1557911414016006715791655)
        ·
          refine ⟨2336867121024010073687483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1557911414016006715791655 2336867121024010073687483)
          ·
            refine ⟨3505300681536015110531225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336867121024010073687483 3505300681536015110531225)
            ·
              refine ⟨2628975511152011332898419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3505300681536015110531225 2628975511152011332898419)
              ·
                refine ⟨3943463266728016999347629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2628975511152011332898419 3943463266728016999347629)
                ·
                  refine ⟨1478798725023006374755361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3943463266728016999347629 1478798725023006374755361)
                  ·
                    refine ⟨1109099043767254781066521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1478798725023006374755361 1109099043767254781066521)
                    ·
                      refine ⟨831824282825441085799891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1109099043767254781066521 831824282825441085799891)
                      ·
                        rfl

theorem cell23_1619972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_1619972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1619972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1619972 prefixEnd_1619972 := by exact prefixLift 1619972
  have htrace : WordTrace (prefixWord ++ tailWord_1619972) baseStart_1619972 baseEnd_1619972 := by
    simpa [prefixWord, tailWord_1619972, baseEnd_1619972] using wordTrace_append hprefix tailTrace_1619972
  have hstable : (prefixWord ++ tailWord_1619972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619972).length < 2 ^ (prefixWord ++ tailWord_1619972).sum := by decide
  have hdescent : baseEnd_1619972 < baseStart_1619972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620028 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 4, 2, 2]
def baseStart_1620028 : Nat := 118140960795 + 1620028 * 2 ^ 59
def prefixEnd_1620028 : Nat := 4983230072969 + 3 ^ 40 * 1620028 * 2
def baseEnd_1620028 : Nat := 831853037742092866699633

theorem tailTrace_1620028 : CollatzResearch.WordTrace tailWord_1620028 prefixEnd_1620028 831853037742092866699633 := by
  unfold tailWord_1620028
  simp only [CollatzResearch.WordTrace]
  refine ⟨29543637687461354799994369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39391516916615139733325825 29543637687461354799994369)
  ·
    refine ⟨22157728265596016099995777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29543637687461354799994369 22157728265596016099995777)
    ·
      refine ⟨16618296199197012074996833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22157728265596016099995777 16618296199197012074996833)
      ·
        refine ⟨12463722149397759056247625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16618296199197012074996833 12463722149397759056247625)
        ·
          refine ⟨9347791612048319292185719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12463722149397759056247625 9347791612048319292185719)
          ·
            refine ⟨14021687418072478938278579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9347791612048319292185719 14021687418072478938278579)
            ·
              refine ⟨21032531127108718407417869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14021687418072478938278579 21032531127108718407417869)
              ·
                refine ⟨7887199172665769402781701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21032531127108718407417869 7887199172665769402781701)
                ·
                  refine ⟨1478849844874831763021569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7887199172665769402781701 1478849844874831763021569)
                  ·
                    refine ⟨1109137383656123822266177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1478849844874831763021569 1109137383656123822266177)
                    ·
                      refine ⟨831853037742092866699633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1109137383656123822266177 831853037742092866699633)
                      ·
                        rfl

theorem cell23_1620028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_1620028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620028 prefixEnd_1620028 := by exact prefixLift 1620028
  have htrace : WordTrace (prefixWord ++ tailWord_1620028) baseStart_1620028 baseEnd_1620028 := by
    simpa [prefixWord, tailWord_1620028, baseEnd_1620028] using wordTrace_append hprefix tailTrace_1620028
  have hstable : (prefixWord ++ tailWord_1620028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620028).length < 2 ^ (prefixWord ++ tailWord_1620028).sum := by decide
  have hdescent : baseEnd_1620028 < baseStart_1620028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620145 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 3, 4]
def baseStart_1620145 : Nat := 118140960795 + 1620145 * 2 ^ 59
def prefixEnd_1620145 : Nat := 4983230072969 + 3 ^ 40 * 1620145 * 2
def baseEnd_1620145 : Nat := 277304371659556302978865

theorem tailTrace_1620145 : CollatzResearch.WordTrace tailWord_1620145 prefixEnd_1620145 277304371659556302978865 := by
  unfold tailWord_1620145
  simp only [CollatzResearch.WordTrace]
  refine ⟨59091542715498838581997889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39394361810332559054665259 59091542715498838581997889)
  ·
    refine ⟨44318657036624128936498417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59091542715498838581997889 44318657036624128936498417)
    ·
      refine ⟨33238992777468096702373813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44318657036624128936498417 33238992777468096702373813)
      ·
        refine ⟨3116155572887634065847545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33238992777468096702373813 3116155572887634065847545)
        ·
          refine ⟨2337116679665725549385659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3116155572887634065847545 2337116679665725549385659)
          ·
            refine ⟨3505675019498588324078489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2337116679665725549385659 3505675019498588324078489)
            ·
              refine ⟨2629256264623941243058867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3505675019498588324078489 2629256264623941243058867)
              ·
                refine ⟨3943884396935911864588301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2629256264623941243058867 3943884396935911864588301)
                ·
                  refine ⟨1478956648850966949220613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3943884396935911864588301 1478956648850966949220613)
                  ·
                    refine ⟨277304371659556302978865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1478956648850966949220613 277304371659556302978865)
                    ·
                      rfl

theorem cell23_1620145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_1620145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620145 prefixEnd_1620145 := by exact prefixLift 1620145
  have htrace : WordTrace (prefixWord ++ tailWord_1620145) baseStart_1620145 baseEnd_1620145 := by
    simpa [prefixWord, tailWord_1620145, baseEnd_1620145] using wordTrace_append hprefix tailTrace_1620145
  have hstable : (prefixWord ++ tailWord_1620145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620145).length < 2 ^ (prefixWord ++ tailWord_1620145).sum := by decide
  have hdescent : baseEnd_1620145 < baseStart_1620145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620162 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_1620162 : Nat := 118140960795 + 1620162 * 2 ^ 59
def prefixEnd_1620162 : Nat := 4983230072969 + 3 ^ 40 * 1620162 * 2
def baseEnd_1620162 : Nat := 277307281383265114141339

theorem tailTrace_1620162 : CollatzResearch.WordTrace tailWord_1620162 prefixEnd_1620162 277307281383265114141339 := by
  unfold tailWord_1620162
  simp only [CollatzResearch.WordTrace]
  refine ⟨14773040689109312621341685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39394775170958166990244493 14773040689109312621341685)
  ·
    refine ⟨1384972564603998058250783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14773040689109312621341685 1384972564603998058250783)
    ·
      refine ⟨2077458846905997087376175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1384972564603998058250783 2077458846905997087376175)
      ·
        refine ⟨3116188270358995631064263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2077458846905997087376175 3116188270358995631064263)
        ·
          refine ⟨4674282405538493446596395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3116188270358995631064263 4674282405538493446596395)
          ·
            refine ⟨7011423608307740169894593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4674282405538493446596395 7011423608307740169894593)
            ·
              refine ⟨5258567706230805127420945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7011423608307740169894593 5258567706230805127420945)
              ·
                refine ⟨3943925779673103845565709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5258567706230805127420945 3943925779673103845565709)
                ·
                  refine ⟨1478972167377413942087141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3943925779673103845565709 1478972167377413942087141)
                  ·
                    refine ⟨277307281383265114141339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1478972167377413942087141 277307281383265114141339)
                    ·
                      rfl

theorem cell23_1620162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_1620162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620162 prefixEnd_1620162 := by exact prefixLift 1620162
  have htrace : WordTrace (prefixWord ++ tailWord_1620162) baseStart_1620162 baseEnd_1620162 := by
    simpa [prefixWord, tailWord_1620162, baseEnd_1620162] using wordTrace_append hprefix tailTrace_1620162
  have hstable : (prefixWord ++ tailWord_1620162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620162).length < 2 ^ (prefixWord ++ tailWord_1620162).sum := by decide
  have hdescent : baseEnd_1620162 < baseStart_1620162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620191 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 4]
def baseStart_1620191 : Nat := 118140960795 + 1620191 * 2 ^ 59
def prefixEnd_1620191 : Nat := 4983230072969 + 3 ^ 40 * 1620191 * 2
def baseEnd_1620191 : Nat := 831936735088775728961383

theorem tailTrace_1620191 : CollatzResearch.WordTrace tailWord_1620191 prefixEnd_1620191 831936735088775728961383 := by
  unfold tailWord_1620191
  simp only [CollatzResearch.WordTrace]
  refine ⟨59093220473332188438172427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39395480315554792292114951 59093220473332188438172427)
  ·
    refine ⟨88639830709998282657258641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59093220473332188438172427 88639830709998282657258641)
    ·
      refine ⟨66479873032498711992943981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88639830709998282657258641 66479873032498711992943981)
      ·
        refine ⟨24929952387187016997353993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66479873032498711992943981 24929952387187016997353993)
        ·
          refine ⟨18697464290390262748015495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24929952387187016997353993 18697464290390262748015495)
          ·
            refine ⟨28046196435585394122023243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18697464290390262748015495 28046196435585394122023243)
            ·
              refine ⟨42069294653378091183034865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28046196435585394122023243 42069294653378091183034865)
              ·
                refine ⟨31551970990033568387276149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42069294653378091183034865 31551970990033568387276149)
                ·
                  refine ⟨2957997280315647036307139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31551970990033568387276149 2957997280315647036307139)
                  ·
                    refine ⟨4436995920473470554460709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2957997280315647036307139 4436995920473470554460709)
                    ·
                      refine ⟨831936735088775728961383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4436995920473470554460709 831936735088775728961383)
                      ·
                        rfl

theorem cell23_1620191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_1620191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620191 prefixEnd_1620191 := by exact prefixLift 1620191
  have htrace : WordTrace (prefixWord ++ tailWord_1620191) baseStart_1620191 baseEnd_1620191 := by
    simpa [prefixWord, tailWord_1620191, baseEnd_1620191] using wordTrace_append hprefix tailTrace_1620191
  have hstable : (prefixWord ++ tailWord_1620191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620191).length < 2 ^ (prefixWord ++ tailWord_1620191).sum := by decide
  have hdescent : baseEnd_1620191 < baseStart_1620191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620211 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 5]
def baseStart_1620211 : Nat := 118140960795 + 1620211 * 2 ^ 59
def prefixEnd_1620211 : Nat := 4983230072969 + 3 ^ 40 * 1620211 * 2
def baseEnd_1620211 : Nat := 831947004701865650711291

theorem tailTrace_1620211 : CollatzResearch.WordTrace tailWord_1620211 prefixEnd_1620211 831947004701865650711291 := by
  unfold tailWord_1620211
  simp only [CollatzResearch.WordTrace]
  refine ⟨59093949933259731853900487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39395966622173154569266991 59093949933259731853900487)
  ·
    refine ⟨88640924899889597780850731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59093949933259731853900487 88640924899889597780850731)
    ·
      refine ⟨132961387349834396671276097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88640924899889597780850731 132961387349834396671276097)
      ·
        refine ⟨99721040512375797503457073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132961387349834396671276097 99721040512375797503457073)
        ·
          refine ⟨74790780384281848127592805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99721040512375797503457073 74790780384281848127592805)
          ·
            refine ⟨14023271322052846523923651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74790780384281848127592805 14023271322052846523923651)
            ·
              refine ⟨21034906983079269785885477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14023271322052846523923651 21034906983079269785885477)
              ·
                refine ⟨3944045059327363084853527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21034906983079269785885477 3944045059327363084853527)
                ·
                  refine ⟨5916067588991044627280291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3944045059327363084853527 5916067588991044627280291)
                  ·
                    refine ⟨8874101383486566940920437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5916067588991044627280291 8874101383486566940920437)
                    ·
                      refine ⟨831947004701865650711291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8874101383486566940920437 831947004701865650711291)
                      ·
                        rfl

theorem cell23_1620211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 5].length) (baseStart_1620211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620211 prefixEnd_1620211 := by exact prefixLift 1620211
  have htrace : WordTrace (prefixWord ++ tailWord_1620211) baseStart_1620211 baseEnd_1620211 := by
    simpa [prefixWord, tailWord_1620211, baseEnd_1620211] using wordTrace_append hprefix tailTrace_1620211
  have hstable : (prefixWord ++ tailWord_1620211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620211).length < 2 ^ (prefixWord ++ tailWord_1620211).sum := by decide
  have hdescent : baseEnd_1620211 < baseStart_1620211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620221 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_1620221 : Nat := 118140960795 + 1620221 * 2 ^ 59
def prefixEnd_1620221 : Nat := 4983230072969 + 3 ^ 40 * 1620221 * 2
def baseEnd_1620221 : Nat := 831952139508410611586245

theorem tailTrace_1620221 : CollatzResearch.WordTrace tailWord_1620221 prefixEnd_1620221 831952139508410611586245 := by
  unfold tailWord_1620221
  simp only [CollatzResearch.WordTrace]
  refine ⟨59094314663223503561764517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39396209775482335707843011 59094314663223503561764517)
  ·
    refine ⟨11080183999354406917830847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59094314663223503561764517 11080183999354406917830847)
    ·
      refine ⟨16620275999031610376746271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11080183999354406917830847 16620275999031610376746271)
      ·
        refine ⟨24930413998547415565119407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16620275999031610376746271 24930413998547415565119407)
        ·
          refine ⟨37395620997821123347679111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24930413998547415565119407 37395620997821123347679111)
          ·
            refine ⟨56093431496731685021518667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37395620997821123347679111 56093431496731685021518667)
            ·
              refine ⟨84140147245097527532278001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56093431496731685021518667 84140147245097527532278001)
              ·
                refine ⟨63105110433823145649208501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84140147245097527532278001 63105110433823145649208501)
                ·
                  refine ⟨5916104103170919904613297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63105110433823145649208501 5916104103170919904613297)
                  ·
                    refine ⟨4437078077378189928459973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5916104103170919904613297 4437078077378189928459973)
                    ·
                      refine ⟨831952139508410611586245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4437078077378189928459973 831952139508410611586245)
                      ·
                        rfl

theorem cell23_1620221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_1620221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620221 prefixEnd_1620221 := by exact prefixLift 1620221
  have htrace : WordTrace (prefixWord ++ tailWord_1620221) baseStart_1620221 baseEnd_1620221 := by
    simpa [prefixWord, tailWord_1620221, baseEnd_1620221] using wordTrace_append hprefix tailTrace_1620221
  have hstable : (prefixWord ++ tailWord_1620221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620221).length < 2 ^ (prefixWord ++ tailWord_1620221).sum := by decide
  have hdescent : baseEnd_1620221 < baseStart_1620221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620225 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 5, 2, 2]
def baseStart_1620225 : Nat := 118140960795 + 1620225 * 2 ^ 59
def prefixEnd_1620225 : Nat := 4983230072969 + 3 ^ 40 * 1620225 * 2
def baseEnd_1620225 : Nat := 831954193431028595936227

theorem tailTrace_1620225 : CollatzResearch.WordTrace tailWord_1620225 prefixEnd_1620225 831954193431028595936227 := by
  unfold tailWord_1620225
  simp only [CollatzResearch.WordTrace]
  refine ⟨59094460555209012244910129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39396307036806008163273419 59094460555209012244910129)
  ·
    refine ⟨44320845416406759183682597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59094460555209012244910129 44320845416406759183682597)
    ·
      refine ⟨8310158515576267346940487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44320845416406759183682597 8310158515576267346940487)
      ·
        refine ⟨12465237773364401020410731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8310158515576267346940487 12465237773364401020410731)
        ·
          refine ⟨18697856660046601530616097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12465237773364401020410731 18697856660046601530616097)
          ·
            refine ⟨14023392495034951147962073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18697856660046601530616097 14023392495034951147962073)
            ·
              refine ⟨10517544371276213360971555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14023392495034951147962073 10517544371276213360971555)
              ·
                refine ⟨15776316556914320041457333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10517544371276213360971555 15776316556914320041457333)
                ·
                  refine ⟨1479029677210717503886625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15776316556914320041457333 1479029677210717503886625)
                  ·
                    refine ⟨1109272257908038127914969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1479029677210717503886625 1109272257908038127914969)
                    ·
                      refine ⟨831954193431028595936227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1109272257908038127914969 831954193431028595936227)
                      ·
                        rfl

theorem cell23_1620225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_1620225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620225 prefixEnd_1620225 := by exact prefixLift 1620225
  have htrace : WordTrace (prefixWord ++ tailWord_1620225) baseStart_1620225 baseEnd_1620225 := by
    simpa [prefixWord, tailWord_1620225, baseEnd_1620225] using wordTrace_append hprefix tailTrace_1620225
  have hstable : (prefixWord ++ tailWord_1620225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620225).length < 2 ^ (prefixWord ++ tailWord_1620225).sum := by decide
  have hdescent : baseEnd_1620225 < baseStart_1620225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620238 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_1620238 : Nat := 118140960795 + 1620238 * 2 ^ 59
def prefixEnd_1620238 : Nat := 4983230072969 + 3 ^ 40 * 1620238 * 2
def baseEnd_1620238 : Nat := 831960868679537045073667

theorem tailTrace_1620238 : CollatzResearch.WordTrace tailWord_1620238 prefixEnd_1620238 831960868679537045073667 := by
  unfold tailWord_1620238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7386866838020239433141671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39396623136107943643422245 7386866838020239433141671)
  ·
    refine ⟨11080300257030359149712507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7386866838020239433141671 11080300257030359149712507)
    ·
      refine ⟨16620450385545538724568761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11080300257030359149712507 16620450385545538724568761)
      ·
        refine ⟨12465337789159154043426571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16620450385545538724568761 12465337789159154043426571)
        ·
          refine ⟨18698006683738731065139857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12465337789159154043426571 18698006683738731065139857)
          ·
            refine ⟨14023505012804048298854893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18698006683738731065139857 14023505012804048298854893)
            ·
              refine ⟨5258814379801518112070585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14023505012804048298854893 5258814379801518112070585)
              ·
                refine ⟨3944110784851138584052939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5258814379801518112070585 3944110784851138584052939)
                ·
                  refine ⟨5916166177276707876079409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3944110784851138584052939 5916166177276707876079409)
                  ·
                    refine ⟨4437124632957530907059557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5916166177276707876079409 4437124632957530907059557)
                    ·
                      refine ⟨831960868679537045073667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4437124632957530907059557 831960868679537045073667)
                      ·
                        rfl

theorem cell23_1620238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_1620238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620238 prefixEnd_1620238 := by exact prefixLift 1620238
  have htrace : WordTrace (prefixWord ++ tailWord_1620238) baseStart_1620238 baseEnd_1620238 := by
    simpa [prefixWord, tailWord_1620238, baseEnd_1620238] using wordTrace_append hprefix tailTrace_1620238
  have hstable : (prefixWord ++ tailWord_1620238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620238).length < 2 ^ (prefixWord ++ tailWord_1620238).sum := by decide
  have hdescent : baseEnd_1620238 < baseStart_1620238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620253 : List Nat := [1, 4, 2, 3, 3, 1, 2, 2, 1, 1, 3]
def baseStart_1620253 : Nat := 118140960795 + 1620253 * 2 ^ 59
def prefixEnd_1620253 : Nat := 4983230072969 + 3 ^ 40 * 1620253 * 2
def baseEnd_1620253 : Nat := 831968570889354486386099

theorem tailTrace_1620253 : CollatzResearch.WordTrace tailWord_1620253 prefixEnd_1620253 831968570889354486386099 := by
  unfold tailWord_1620253
  simp only [CollatzResearch.WordTrace]
  refine ⟨59095481799107573026929413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39396987866071715351286275 59095481799107573026929413)
  ·
    refine ⟨11080402837332669942549265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59095481799107573026929413 11080402837332669942549265)
    ·
      refine ⟨8310302127999502456911949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11080402837332669942549265 8310302127999502456911949)
      ·
        refine ⟨3116363297999813421341981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8310302127999502456911949 3116363297999813421341981)
        ·
          refine ⟨1168636236749930033003243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3116363297999813421341981 1168636236749930033003243)
          ·
            refine ⟨1752954355124895049504865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168636236749930033003243 1752954355124895049504865)
            ·
              refine ⟨1314715766343671287128649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1752954355124895049504865 1314715766343671287128649)
              ·
                refine ⟨986036824757753465346487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314715766343671287128649 986036824757753465346487)
                ·
                  refine ⟨1479055237136630198019731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986036824757753465346487 1479055237136630198019731)
                  ·
                    refine ⟨2218582855704945297029597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1479055237136630198019731 2218582855704945297029597)
                    ·
                      refine ⟨831968570889354486386099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2218582855704945297029597 831968570889354486386099)
                      ·
                        rfl

theorem cell23_1620253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_1620253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620253 prefixEnd_1620253 := by exact prefixLift 1620253
  have htrace : WordTrace (prefixWord ++ tailWord_1620253) baseStart_1620253 baseEnd_1620253 := by
    simpa [prefixWord, tailWord_1620253, baseEnd_1620253] using wordTrace_append hprefix tailTrace_1620253
  have hstable : (prefixWord ++ tailWord_1620253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620253).length < 2 ^ (prefixWord ++ tailWord_1620253).sum := by decide
  have hdescent : baseEnd_1620253 < baseStart_1620253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620275 : List Nat := [1, 1, 1, 2, 5, 1, 1, 5, 2, 1, 3]
def baseStart_1620275 : Nat := 118140960795 + 1620275 * 2 ^ 59
def prefixEnd_1620275 : Nat := 4983230072969 + 3 ^ 40 * 1620275 * 2
def baseEnd_1620275 : Nat := 831979867463753400310997

theorem tailTrace_1620275 : CollatzResearch.WordTrace tailWord_1620275 prefixEnd_1620275 831979867463753400310997 := by
  unfold tailWord_1620275
  simp only [CollatzResearch.WordTrace]
  refine ⟨59096284205027870784230279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39397522803351913856153519 59096284205027870784230279)
  ·
    refine ⟨88644426307541806176345419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59096284205027870784230279 88644426307541806176345419)
    ·
      refine ⟨132966639461312709264518129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88644426307541806176345419 132966639461312709264518129)
      ·
        refine ⟨99724979595984531948388597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132966639461312709264518129 99724979595984531948388597)
        ·
          refine ⟨9349216837123549870161431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99724979595984531948388597 9349216837123549870161431)
          ·
            refine ⟨14023825255685324805242147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9349216837123549870161431 14023825255685324805242147)
            ·
              refine ⟨21035737883527987207863221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14023825255685324805242147 21035737883527987207863221)
              ·
                refine ⟨1972100426580748800737177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21035737883527987207863221 1972100426580748800737177)
                ·
                  refine ⟨1479075319935561600552883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1972100426580748800737177 1479075319935561600552883)
                  ·
                    refine ⟨2218612979903342400829325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1479075319935561600552883 2218612979903342400829325)
                    ·
                      refine ⟨831979867463753400310997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2218612979903342400829325 831979867463753400310997)
                      ·
                        rfl

theorem cell23_1620275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 1, 3].length) (baseStart_1620275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620275 prefixEnd_1620275 := by exact prefixLift 1620275
  have htrace : WordTrace (prefixWord ++ tailWord_1620275) baseStart_1620275 baseEnd_1620275 := by
    simpa [prefixWord, tailWord_1620275, baseEnd_1620275] using wordTrace_append hprefix tailTrace_1620275
  have hstable : (prefixWord ++ tailWord_1620275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620275).length < 2 ^ (prefixWord ++ tailWord_1620275).sum := by decide
  have hdescent : baseEnd_1620275 < baseStart_1620275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620308 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_1620308 : Nat := 118140960795 + 1620308 * 2 ^ 59
def prefixEnd_1620308 : Nat := 4983230072969 + 3 ^ 40 * 1620308 * 2
def baseEnd_1620308 : Nat := 277332270775117257066115

theorem tailTrace_1620308 : CollatzResearch.WordTrace tailWord_1620308 prefixEnd_1620308 277332270775117257066115 := by
  unfold tailWord_1620308
  simp only [CollatzResearch.WordTrace]
  refine ⟨29548743906954158710090789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39398325209272211613454385 29548743906954158710090789)
  ·
    refine ⟨5540389482553904758142023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29548743906954158710090789 5540389482553904758142023)
    ·
      refine ⟨8310584223830857137213035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5540389482553904758142023 8310584223830857137213035)
      ·
        refine ⟨12465876335746285705819553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8310584223830857137213035 12465876335746285705819553)
        ·
          refine ⟨9349407251809714279364665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12465876335746285705819553 9349407251809714279364665)
          ·
            refine ⟨7012055438857285709523499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9349407251809714279364665 7012055438857285709523499)
            ·
              refine ⟨10518083158285928564285249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7012055438857285709523499 10518083158285928564285249)
              ·
                refine ⟨7888562368714446423213937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10518083158285928564285249 7888562368714446423213937)
                ·
                  refine ⟨5916421776535834817410453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7888562368714446423213937 5916421776535834817410453)
                  ·
                    refine ⟨277332270775117257066115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5916421776535834817410453 277332270775117257066115)
                    ·
                      rfl

theorem cell23_1620308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_1620308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620308 prefixEnd_1620308 := by exact prefixLift 1620308
  have htrace : WordTrace (prefixWord ++ tailWord_1620308) baseStart_1620308 baseEnd_1620308 := by
    simpa [prefixWord, tailWord_1620308, baseEnd_1620308] using wordTrace_append hprefix tailTrace_1620308
  have hstable : (prefixWord ++ tailWord_1620308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620308).length < 2 ^ (prefixWord ++ tailWord_1620308).sum := by decide
  have hdescent : baseEnd_1620308 < baseStart_1620308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620309 : List Nat := [1, 3, 2, 2, 4, 2, 1, 2, 2, 1, 3]
def baseStart_1620309 : Nat := 118140960795 + 1620309 * 2 ^ 59
def prefixEnd_1620309 : Nat := 4983230072969 + 3 ^ 40 * 1620309 * 2
def baseEnd_1620309 : Nat := 831997325806006267285841

theorem tailTrace_1620309 : CollatzResearch.WordTrace tailWord_1620309 prefixEnd_1620309 831997325806006267285841 := by
  unfold tailWord_1620309
  simp only [CollatzResearch.WordTrace]
  refine ⟨59097524286904694590967981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39398349524603129727311987 59097524286904694590967981)
  ·
    refine ⟨22161571607589260471612993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59097524286904694590967981 22161571607589260471612993)
    ·
      refine ⟨16621178705691945353709745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22161571607589260471612993 16621178705691945353709745)
      ·
        refine ⟨12465884029268959015282309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16621178705691945353709745 12465884029268959015282309)
        ·
          refine ⟨2337353255487929815365433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12465884029268959015282309 2337353255487929815365433)
          ·
            refine ⟨1753014941615947361524075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2337353255487929815365433 1753014941615947361524075)
            ·
              refine ⟨2629522412423921042286113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753014941615947361524075 2629522412423921042286113)
              ·
                refine ⟨1972141809317940781714585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2629522412423921042286113 1972141809317940781714585)
                ·
                  refine ⟨1479106356988455586285939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1972141809317940781714585 1479106356988455586285939)
                  ·
                    refine ⟨2218659535482683379428909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1479106356988455586285939 2218659535482683379428909)
                    ·
                      refine ⟨831997325806006267285841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2218659535482683379428909 831997325806006267285841)
                      ·
                        rfl

theorem cell23_1620309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_1620309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620309 prefixEnd_1620309 := by exact prefixLift 1620309
  have htrace : WordTrace (prefixWord ++ tailWord_1620309) baseStart_1620309 baseEnd_1620309 := by
    simpa [prefixWord, tailWord_1620309, baseEnd_1620309] using wordTrace_append hprefix tailTrace_1620309
  have hstable : (prefixWord ++ tailWord_1620309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620309).length < 2 ^ (prefixWord ++ tailWord_1620309).sum := by decide
  have hdescent : baseEnd_1620309 < baseStart_1620309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620338 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 7]
def baseStart_1620338 : Nat := 118140960795 + 1620338 * 2 ^ 59
def prefixEnd_1620338 : Nat := 4983230072969 + 3 ^ 40 * 1620338 * 2
def baseEnd_1620338 : Nat := 92445801860554072647023

theorem tailTrace_1620338 : CollatzResearch.WordTrace tailWord_1620338 prefixEnd_1620338 92445801860554072647023 := by
  unfold tailWord_1620338
  simp only [CollatzResearch.WordTrace]
  refine ⟨14774645500949908135943417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39399054669199755029182445 14774645500949908135943417)
  ·
    refine ⟨11080984125712431101957563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14774645500949908135943417 11080984125712431101957563)
    ·
      refine ⟨16621476188568646652936345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11080984125712431101957563 16621476188568646652936345)
      ·
        refine ⟨12466107141426484989702259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16621476188568646652936345 12466107141426484989702259)
        ·
          refine ⟨18699160712139727484553389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12466107141426484989702259 18699160712139727484553389)
          ·
            refine ⟨7012185267052397806707521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18699160712139727484553389 7012185267052397806707521)
            ·
              refine ⟨5259138950289298355030641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7012185267052397806707521 5259138950289298355030641)
              ·
                refine ⟨3944354212716973766272981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5259138950289298355030641 3944354212716973766272981)
                ·
                  refine ⟨92445801860554072647023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3944354212716973766272981 92445801860554072647023)
                  ·
                    rfl

theorem cell23_1620338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_1620338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620338 prefixEnd_1620338 := by exact prefixLift 1620338
  have htrace : WordTrace (prefixWord ++ tailWord_1620338) baseStart_1620338 baseEnd_1620338 := by
    simpa [prefixWord, tailWord_1620338, baseEnd_1620338] using wordTrace_append hprefix tailTrace_1620338
  have hstable : (prefixWord ++ tailWord_1620338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620338).length < 2 ^ (prefixWord ++ tailWord_1620338).sum := by decide
  have hdescent : baseEnd_1620338 < baseStart_1620338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620348 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 4, 3, 3]
def baseStart_1620348 : Nat := 118140960795 + 1620348 * 2 ^ 59
def prefixEnd_1620348 : Nat := 4983230072969 + 3 ^ 40 * 1620348 * 2
def baseEnd_1620348 : Nat := 832017351551531614698161

theorem tailTrace_1620348 : CollatzResearch.WordTrace tailWord_1620348 prefixEnd_1620348 832017351551531614698161 := by
  unfold tailWord_1620348
  simp only [CollatzResearch.WordTrace]
  refine ⟨29549473366881702125818849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39399297822508936167758465 29549473366881702125818849)
  ·
    refine ⟨22162105025161276594364137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29549473366881702125818849 22162105025161276594364137)
    ·
      refine ⟨16621578768870957445773103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22162105025161276594364137 16621578768870957445773103)
      ·
        refine ⟨24932368153306436168659655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16621578768870957445773103 24932368153306436168659655)
        ·
          refine ⟨37398552229959654252989483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24932368153306436168659655 37398552229959654252989483)
          ·
            refine ⟨56097828344939481379484225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37398552229959654252989483 56097828344939481379484225)
            ·
              refine ⟨42073371258704611034613169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56097828344939481379484225 42073371258704611034613169)
              ·
                refine ⟨31555028444028458275959877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42073371258704611034613169 31555028444028458275959877)
                ·
                  refine ⟨5916567833255335926742477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31555028444028458275959877 5916567833255335926742477)
                  ·
                    refine ⟨2218712937470750972528429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5916567833255335926742477 2218712937470750972528429)
                    ·
                      refine ⟨832017351551531614698161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2218712937470750972528429 832017351551531614698161)
                      ·
                        rfl

theorem cell23_1620348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_1620348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620348 prefixEnd_1620348 := by exact prefixLift 1620348
  have htrace : WordTrace (prefixWord ++ tailWord_1620348) baseStart_1620348 baseEnd_1620348 := by
    simpa [prefixWord, tailWord_1620348, baseEnd_1620348] using wordTrace_append hprefix tailTrace_1620348
  have hstable : (prefixWord ++ tailWord_1620348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620348).length < 2 ^ (prefixWord ++ tailWord_1620348).sum := by decide
  have hdescent : baseEnd_1620348 < baseStart_1620348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620371 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 8]
def baseStart_1620371 : Nat := 118140960795 + 1620371 * 2 ^ 59
def prefixEnd_1620371 : Nat := 4983230072969 + 3 ^ 40 * 1620371 * 2
def baseEnd_1620371 : Nat := 832029161606585024710555

theorem tailTrace_1620371 : CollatzResearch.WordTrace tailWord_1620371 prefixEnd_1620371 832029161606585024710555 := by
  unfold tailWord_1620371
  simp only [CollatzResearch.WordTrace]
  refine ⟨59099785612680079179724967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39399857075120052786483311 59099785612680079179724967)
  ·
    refine ⟨88649678419020118769587451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59099785612680079179724967 88649678419020118769587451)
    ·
      refine ⟨132974517628530178154381177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88649678419020118769587451 132974517628530178154381177)
      ·
        refine ⟨99730888221397633615785883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132974517628530178154381177 99730888221397633615785883)
        ·
          refine ⟨149596332332096450423678825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99730888221397633615785883 149596332332096450423678825)
          ·
            refine ⟨112197249249072337817759119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149596332332096450423678825 112197249249072337817759119)
            ·
              refine ⟨168295873873608506726638679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112197249249072337817759119 168295873873608506726638679)
              ·
                refine ⟨252443810810412760089958019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168295873873608506726638679 252443810810412760089958019)
                ·
                  refine ⟨378665716215619140134937029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252443810810412760089958019 378665716215619140134937029)
                  ·
                    refine ⟨70999821790428588775300693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 378665716215619140134937029 70999821790428588775300693)
                    ·
                      refine ⟨832029161606585024710555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 70999821790428588775300693 832029161606585024710555)
                      ·
                        rfl

theorem cell23_1620371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_1620371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620371 prefixEnd_1620371 := by exact prefixLift 1620371
  have htrace : WordTrace (prefixWord ++ tailWord_1620371) baseStart_1620371 baseEnd_1620371 := by
    simpa [prefixWord, tailWord_1620371, baseEnd_1620371] using wordTrace_append hprefix tailTrace_1620371
  have hstable : (prefixWord ++ tailWord_1620371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620371).length < 2 ^ (prefixWord ++ tailWord_1620371).sum := by decide
  have hdescent : baseEnd_1620371 < baseStart_1620371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620372 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 7]
def baseStart_1620372 : Nat := 118140960795 + 1620372 * 2 ^ 59
def prefixEnd_1620372 : Nat := 4983230072969 + 3 ^ 40 * 1620372 * 2
def baseEnd_1620372 : Nat := 92447741676359946755339

theorem tailTrace_1620372 : CollatzResearch.WordTrace tailWord_1620372 prefixEnd_1620372 92447741676359946755339 := by
  unfold tailWord_1620372
  simp only [CollatzResearch.WordTrace]
  refine ⟨29549911042838228175255685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39399881390450970900340913 29549911042838228175255685)
  ·
    refine ⟨5540608320532167782860441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29549911042838228175255685 5540608320532167782860441)
    ·
      refine ⟨4155456240399125837145331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5540608320532167782860441 4155456240399125837145331)
      ·
        refine ⟨6233184360598688755717997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4155456240399125837145331 6233184360598688755717997)
        ·
          refine ⟨2337444135224508283394249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6233184360598688755717997 2337444135224508283394249)
          ·
            refine ⟨1753083101418381212545687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2337444135224508283394249 1753083101418381212545687)
            ·
              refine ⟨2629624652127571818818531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753083101418381212545687 2629624652127571818818531)
              ·
                refine ⟨3944436978191357728227797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2629624652127571818818531 3944436978191357728227797)
                ·
                  refine ⟨92447741676359946755339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3944436978191357728227797 92447741676359946755339)
                  ·
                    rfl

theorem cell23_1620372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_1620372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620372 prefixEnd_1620372 := by exact prefixLift 1620372
  have htrace : WordTrace (prefixWord ++ tailWord_1620372) baseStart_1620372 baseEnd_1620372 := by
    simpa [prefixWord, tailWord_1620372, baseEnd_1620372] using wordTrace_append hprefix tailTrace_1620372
  have hstable : (prefixWord ++ tailWord_1620372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620372).length < 2 ^ (prefixWord ++ tailWord_1620372).sum := by decide
  have hdescent : baseEnd_1620372 < baseStart_1620372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620378 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7]
def baseStart_1620378 : Nat := 118140960795 + 1620378 * 2 ^ 59
def prefixEnd_1620378 : Nat := 4983230072969 + 3 ^ 40 * 1620378 * 2
def baseEnd_1620378 : Nat := 832032755971166497323023

theorem tailTrace_1620378 : CollatzResearch.WordTrace tailWord_1620378 prefixEnd_1620378 832032755971166497323023 := by
  unfold tailWord_1620378
  simp only [CollatzResearch.WordTrace]
  refine ⟨14775010230913679843807447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39400027282436479583486525 14775010230913679843807447)
  ·
    refine ⟨22162515346370519765711171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14775010230913679843807447 22162515346370519765711171)
    ·
      refine ⟨33243773019555779648566757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22162515346370519765711171 33243773019555779648566757)
      ·
        refine ⟨6233207441166708684106267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33243773019555779648566757 6233207441166708684106267)
        ·
          refine ⟨9349811161750063026159401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6233207441166708684106267 9349811161750063026159401)
          ·
            refine ⟨7012358371312547269619551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9349811161750063026159401 7012358371312547269619551)
            ·
              refine ⟨10518537556968820904429327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7012358371312547269619551 10518537556968820904429327)
              ·
                refine ⟨15777806335453231356643991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10518537556968820904429327 15777806335453231356643991)
                ·
                  refine ⟨23666709503179847034965987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15777806335453231356643991 23666709503179847034965987)
                  ·
                    refine ⟨35500064254769770552448981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23666709503179847034965987 35500064254769770552448981)
                    ·
                      refine ⟨832032755971166497323023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35500064254769770552448981 832032755971166497323023)
                      ·
                        rfl

theorem cell23_1620378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_1620378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620378 prefixEnd_1620378 := by exact prefixLift 1620378
  have htrace : WordTrace (prefixWord ++ tailWord_1620378) baseStart_1620378 baseEnd_1620378 := by
    simpa [prefixWord, tailWord_1620378, baseEnd_1620378] using wordTrace_append hprefix tailTrace_1620378
  have hstable : (prefixWord ++ tailWord_1620378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620378).length < 2 ^ (prefixWord ++ tailWord_1620378).sum := by decide
  have hdescent : baseEnd_1620378 < baseStart_1620378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620388 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_1620388 : Nat := 118140960795 + 1620388 * 2 ^ 59
def prefixEnd_1620388 : Nat := 4983230072969 + 3 ^ 40 * 1620388 * 2
def baseEnd_1620388 : Nat := 832037890777711458197977

theorem tailTrace_1620388 : CollatzResearch.WordTrace tailWord_1620388 prefixEnd_1620388 832037890777711458197977 := by
  unfold tailWord_1620388
  simp only [CollatzResearch.WordTrace]
  refine ⟨29550202826809245541546909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39400270435745660722062545 29550202826809245541546909)
  ·
    refine ⟨11081326060053467078080091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29550202826809245541546909 11081326060053467078080091)
    ·
      refine ⟨16621989090080200617120137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11081326060053467078080091 16621989090080200617120137)
      ·
        refine ⟨12466491817560150462840103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16621989090080200617120137 12466491817560150462840103)
        ·
          refine ⟨18699737726340225694260155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12466491817560150462840103 18699737726340225694260155)
          ·
            refine ⟨28049606589510338541390233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18699737726340225694260155 28049606589510338541390233)
            ·
              refine ⟨21037204942132753906042675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28049606589510338541390233 21037204942132753906042675)
              ·
                refine ⟨31555807413199130859064013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21037204942132753906042675 31555807413199130859064013)
                ·
                  refine ⟨11833427779949674072149005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31555807413199130859064013 11833427779949674072149005)
                  ·
                    refine ⟨4437535417481127777055877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11833427779949674072149005 4437535417481127777055877)
                    ·
                      refine ⟨832037890777711458197977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4437535417481127777055877 832037890777711458197977)
                      ·
                        rfl

theorem cell23_1620388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_1620388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620388 prefixEnd_1620388 := by exact prefixLift 1620388
  have htrace : WordTrace (prefixWord ++ tailWord_1620388) baseStart_1620388 baseEnd_1620388 := by
    simpa [prefixWord, tailWord_1620388, baseEnd_1620388] using wordTrace_append hprefix tailTrace_1620388
  have hstable : (prefixWord ++ tailWord_1620388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620388).length < 2 ^ (prefixWord ++ tailWord_1620388).sum := by decide
  have hdescent : baseEnd_1620388 < baseStart_1620388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620425 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 2, 2, 3]
def baseStart_1620425 : Nat := 118140960795 + 1620425 * 2 ^ 59
def prefixEnd_1620425 : Nat := 4983230072969 + 3 ^ 40 * 1620425 * 2
def baseEnd_1620425 : Nat := 832056889561927813435307

theorem tailTrace_1620425 : CollatzResearch.WordTrace tailWord_1620425 prefixEnd_1620425 832056889561927813435307 := by
  unfold tailWord_1620425
  simp only [CollatzResearch.WordTrace]
  refine ⟨59101755154484446402190729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39401170102989630934793819 59101755154484446402190729)
  ·
    refine ⟨44326316365863334801643047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59101755154484446402190729 44326316365863334801643047)
    ·
      refine ⟨66489474548795002202464571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44326316365863334801643047 66489474548795002202464571)
      ·
        refine ⟨99734211823192503303696857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66489474548795002202464571 99734211823192503303696857)
        ·
          refine ⟨74800658867394377477772643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99734211823192503303696857 74800658867394377477772643)
          ·
            refine ⟨112200988301091566216658965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74800658867394377477772643 112200988301091566216658965)
            ·
              refine ⟨5259421326613667166405889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112200988301091566216658965 5259421326613667166405889)
              ·
                refine ⟨3944565994960250374804417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5259421326613667166405889 3944565994960250374804417)
                ·
                  refine ⟨2958424496220187781103313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3944565994960250374804417 2958424496220187781103313)
                  ·
                    refine ⟨2218818372165140835827485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2958424496220187781103313 2218818372165140835827485)
                    ·
                      refine ⟨832056889561927813435307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2218818372165140835827485 832056889561927813435307)
                      ·
                        rfl

theorem cell23_1620425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 2, 3].length) (baseStart_1620425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620425 prefixEnd_1620425 := by exact prefixLift 1620425
  have htrace : WordTrace (prefixWord ++ tailWord_1620425) baseStart_1620425 baseEnd_1620425 := by
    simpa [prefixWord, tailWord_1620425, baseEnd_1620425] using wordTrace_append hprefix tailTrace_1620425
  have hstable : (prefixWord ++ tailWord_1620425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620425).length < 2 ^ (prefixWord ++ tailWord_1620425).sum := by decide
  have hdescent : baseEnd_1620425 < baseStart_1620425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620445 : List Nat := [1, 4, 3, 1, 1, 1, 1, 5, 6]
def baseStart_1620445 : Nat := 118140960795 + 1620445 * 2 ^ 59
def prefixEnd_1620445 : Nat := 4983230072969 + 3 ^ 40 * 1620445 * 2
def baseEnd_1620445 : Nat := 92451906575001970576135

theorem tailTrace_1620445 : CollatzResearch.WordTrace tailWord_1620445 prefixEnd_1620445 92451906575001970576135 := by
  unfold tailWord_1620445
  simp only [CollatzResearch.WordTrace]
  refine ⟨59102484614411989817918789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39401656409607993211945859 59102484614411989817918789)
  ·
    refine ⟨11081715865202248090859773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59102484614411989817918789 11081715865202248090859773)
    ·
      refine ⟨4155643449450843034072415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11081715865202248090859773 4155643449450843034072415)
      ·
        refine ⟨6233465174176264551108623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4155643449450843034072415 6233465174176264551108623)
        ·
          refine ⟨9350197761264396826662935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6233465174176264551108623 9350197761264396826662935)
          ·
            refine ⟨14025296641896595239994403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9350197761264396826662935 14025296641896595239994403)
            ·
              refine ⟨21037944962844892859991605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14025296641896595239994403 21037944962844892859991605)
              ·
                refine ⟨1972307340266708705624213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21037944962844892859991605 1972307340266708705624213)
                ·
                  refine ⟨92451906575001970576135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1972307340266708705624213 92451906575001970576135)
                  ·
                    rfl

theorem cell23_1620445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_1620445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620445 prefixEnd_1620445 := by exact prefixLift 1620445
  have htrace : WordTrace (prefixWord ++ tailWord_1620445) baseStart_1620445 baseEnd_1620445 := by
    simpa [prefixWord, tailWord_1620445, baseEnd_1620445] using wordTrace_append hprefix tailTrace_1620445
  have hstable : (prefixWord ++ tailWord_1620445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620445).length < 2 ^ (prefixWord ++ tailWord_1620445).sum := by decide
  have hdescent : baseEnd_1620445 < baseStart_1620445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620466 : List Nat := [3, 2, 1, 4, 2, 1, 2, 3, 1, 4]
def baseStart_1620466 : Nat := 118140960795 + 1620466 * 2 ^ 59
def prefixEnd_1620466 : Nat := 4983230072969 + 3 ^ 40 * 1620466 * 2
def baseEnd_1620466 : Nat := 277359314089587384340873

theorem tailTrace_1620466 : CollatzResearch.WordTrace tailWord_1620466 prefixEnd_1620466 277359314089587384340873 := by
  unfold tailWord_1620466
  simp only [CollatzResearch.WordTrace]
  refine ⟨14775812636833977601108313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39402167031557273602955501 14775812636833977601108313)
  ·
    refine ⟨11081859477625483200831235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14775812636833977601108313 11081859477625483200831235)
    ·
      refine ⟨16622789216438224801246853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11081859477625483200831235 16622789216438224801246853)
      ·
        refine ⟨3116772978082167150233785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16622789216438224801246853 3116772978082167150233785)
        ·
          refine ⟨2337579733561625362675339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3116772978082167150233785 2337579733561625362675339)
          ·
            refine ⟨3506369600342438044013009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2337579733561625362675339 3506369600342438044013009)
            ·
              refine ⟨2629777200256828533009757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3506369600342438044013009 2629777200256828533009757)
              ·
                refine ⟨986166450096310699878659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2629777200256828533009757 986166450096310699878659)
                ·
                  refine ⟨1479249675144466049817989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986166450096310699878659 1479249675144466049817989)
                  ·
                    refine ⟨277359314089587384340873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1479249675144466049817989 277359314089587384340873)
                    ·
                      rfl

theorem cell23_1620466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_1620466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620466 prefixEnd_1620466 := by exact prefixLift 1620466
  have htrace : WordTrace (prefixWord ++ tailWord_1620466) baseStart_1620466 baseEnd_1620466 := by
    simpa [prefixWord, tailWord_1620466, baseEnd_1620466] using wordTrace_append hprefix tailTrace_1620466
  have hstable : (prefixWord ++ tailWord_1620466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620466).length < 2 ^ (prefixWord ++ tailWord_1620466).sum := by decide
  have hdescent : baseEnd_1620466 < baseStart_1620466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620495 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 2, 6, 2]
def baseStart_1620495 : Nat := 118140960795 + 1620495 * 2 ^ 59
def prefixEnd_1620495 : Nat := 4983230072969 + 3 ^ 40 * 1620495 * 2
def baseEnd_1620495 : Nat := 832092833207742539559985

theorem tailTrace_1620495 : CollatzResearch.WordTrace tailWord_1620495 prefixEnd_1620495 832092833207742539559985 := by
  unfold tailWord_1620495
  simp only [CollatzResearch.WordTrace]
  refine ⟨59104308264230848357238939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39402872176153898904825959 59104308264230848357238939)
  ·
    refine ⟨88656462396346272535858409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59104308264230848357238939 88656462396346272535858409)
    ·
      refine ⟨66492346797259704401893807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88656462396346272535858409 66492346797259704401893807)
      ·
        refine ⟨99738520195889556602840711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66492346797259704401893807 99738520195889556602840711)
        ·
          refine ⟨149607780293834334904261067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99738520195889556602840711 149607780293834334904261067)
          ·
            refine ⟨224411670440751502356391601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149607780293834334904261067 224411670440751502356391601)
            ·
              refine ⟨168308752830563626767293701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224411670440751502356391601 168308752830563626767293701)
              ·
                refine ⟨31557891155730680018867569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168308752830563626767293701 31557891155730680018867569)
                ·
                  refine ⟨23668418366798010014150677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31557891155730680018867569 23668418366798010014150677)
                  ·
                    refine ⟨1109457110943656719413313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23668418366798010014150677 1109457110943656719413313)
                    ·
                      refine ⟨832092833207742539559985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1109457110943656719413313 832092833207742539559985)
                      ·
                        rfl

theorem cell23_1620495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 6, 2].length) (baseStart_1620495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620495 prefixEnd_1620495 := by exact prefixLift 1620495
  have htrace : WordTrace (prefixWord ++ tailWord_1620495) baseStart_1620495 baseEnd_1620495 := by
    simpa [prefixWord, tailWord_1620495, baseEnd_1620495] using wordTrace_append hprefix tailTrace_1620495
  have hstable : (prefixWord ++ tailWord_1620495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620495).length < 2 ^ (prefixWord ++ tailWord_1620495).sum := by decide
  have hdescent : baseEnd_1620495 < baseStart_1620495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620522 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 4, 4]
def baseStart_1620522 : Nat := 118140960795 + 1620522 * 2 ^ 59
def prefixEnd_1620522 : Nat := 4983230072969 + 3 ^ 40 * 1620522 * 2
def baseEnd_1620522 : Nat := 277368899061804644640787

theorem tailTrace_1620522 : CollatzResearch.WordTrace tailWord_1620522 prefixEnd_1620522 277368899061804644640787 := by
  unfold tailWord_1620522
  simp only [CollatzResearch.WordTrace]
  refine ⟨14776323258783257992117955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39403528690088687978981213 14776323258783257992117955)
  ·
    refine ⟨22164484888174886988176933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14776323258783257992117955 22164484888174886988176933)
    ·
      refine ⟨4155840916532791310283175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22164484888174886988176933 4155840916532791310283175)
      ·
        refine ⟨6233761374799186965424763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4155840916532791310283175 6233761374799186965424763)
        ·
          refine ⟨9350642062198780448137145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6233761374799186965424763 9350642062198780448137145)
          ·
            refine ⟨7012981546649085336102859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9350642062198780448137145 7012981546649085336102859)
            ·
              refine ⟨10519472319973628004154289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7012981546649085336102859 10519472319973628004154289)
              ·
                refine ⟨7889604239980221003115717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10519472319973628004154289 7889604239980221003115717)
                ·
                  refine ⟨1479300794996291438084197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7889604239980221003115717 1479300794996291438084197)
                  ·
                    refine ⟨277368899061804644640787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1479300794996291438084197 277368899061804644640787)
                    ·
                      rfl

theorem cell23_1620522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_1620522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620522 prefixEnd_1620522 := by exact prefixLift 1620522
  have htrace : WordTrace (prefixWord ++ tailWord_1620522) baseStart_1620522 baseEnd_1620522 := by
    simpa [prefixWord, tailWord_1620522, baseEnd_1620522] using wordTrace_append hprefix tailTrace_1620522
  have hstable : (prefixWord ++ tailWord_1620522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620522).length < 2 ^ (prefixWord ++ tailWord_1620522).sum := by decide
  have hdescent : baseEnd_1620522 < baseStart_1620522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620562 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_1620562 : Nat := 118140960795 + 1620562 * 2 ^ 59
def prefixEnd_1620562 : Nat := 4983230072969 + 3 ^ 40 * 1620562 * 2
def baseEnd_1620562 : Nat := 832127236411593777422177

theorem tailTrace_1620562 : CollatzResearch.WordTrace tailWord_1620562 prefixEnd_1620562 832127236411593777422177 := by
  unfold tailWord_1620562
  simp only [CollatzResearch.WordTrace]
  refine ⟨14776687988747029699981985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39404501303325412533285293 14776687988747029699981985)
  ·
    refine ⟨11082515991560272274986489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14776687988747029699981985 11082515991560272274986489)
    ·
      refine ⟨8311886993670204206239867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11082515991560272274986489 8311886993670204206239867)
      ·
        refine ⟨12467830490505306309359801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8311886993670204206239867 12467830490505306309359801)
        ·
          refine ⟨9350872867878979732019851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12467830490505306309359801 9350872867878979732019851)
          ·
            refine ⟨14026309301818469598029777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9350872867878979732019851 14026309301818469598029777)
            ·
              refine ⟨10519731976363852198522333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14026309301818469598029777 10519731976363852198522333)
              ·
                refine ⟨3944899491136444574445875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10519731976363852198522333 3944899491136444574445875)
                ·
                  refine ⟨5917349236704666861668813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3944899491136444574445875 5917349236704666861668813)
                  ·
                    refine ⟨2219005963764250073125805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5917349236704666861668813 2219005963764250073125805)
                    ·
                      refine ⟨832127236411593777422177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2219005963764250073125805 832127236411593777422177)
                      ·
                        rfl

theorem cell23_1620562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_1620562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620562 prefixEnd_1620562 := by exact prefixLift 1620562
  have htrace : WordTrace (prefixWord ++ tailWord_1620562) baseStart_1620562 baseEnd_1620562 := by
    simpa [prefixWord, tailWord_1620562, baseEnd_1620562] using wordTrace_append hprefix tailTrace_1620562
  have hstable : (prefixWord ++ tailWord_1620562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620562).length < 2 ^ (prefixWord ++ tailWord_1620562).sum := by decide
  have hdescent : baseEnd_1620562 < baseStart_1620562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620597 : List Nat := [1, 3, 4, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_1620597 : Nat := 118140960795 + 1620597 * 2 ^ 59
def prefixEnd_1620597 : Nat := 4983230072969 + 3 ^ 40 * 1620597 * 2
def baseEnd_1620597 : Nat := 832145208234501140484517

theorem tailTrace_1620597 : CollatzResearch.WordTrace tailWord_1620597 prefixEnd_1620597 832145208234501140484517 := by
  unfold tailWord_1620597
  simp only [CollatzResearch.WordTrace]
  refine ⟨59108028509861319777452045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39405352339907546518301363 59108028509861319777452045)
  ·
    refine ⟨22165510691197994916544517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59108028509861319777452045 22165510691197994916544517)
    ·
      refine ⟨4156033254599624046852097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22165510691197994916544517 4156033254599624046852097)
      ·
        refine ⟨3117024940949718035139073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4156033254599624046852097 3117024940949718035139073)
        ·
          refine ⟨2337768705712288526354305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3117024940949718035139073 2337768705712288526354305)
          ·
            refine ⟨1753326529284216394765729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2337768705712288526354305 1753326529284216394765729)
            ·
              refine ⟨1314994896963162296074297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1753326529284216394765729 1314994896963162296074297)
              ·
                refine ⟨986246172722371722055723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314994896963162296074297 986246172722371722055723)
                ·
                  refine ⟨1479369259083557583083585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986246172722371722055723 1479369259083557583083585)
                  ·
                    refine ⟨1109526944312668187312689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1479369259083557583083585 1109526944312668187312689)
                    ·
                      refine ⟨832145208234501140484517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1109526944312668187312689 832145208234501140484517)
                      ·
                        rfl

theorem cell23_1620597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_1620597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620597 prefixEnd_1620597 := by exact prefixLift 1620597
  have htrace : WordTrace (prefixWord ++ tailWord_1620597) baseStart_1620597 baseEnd_1620597 := by
    simpa [prefixWord, tailWord_1620597, baseEnd_1620597] using wordTrace_append hprefix tailTrace_1620597
  have hstable : (prefixWord ++ tailWord_1620597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620597).length < 2 ^ (prefixWord ++ tailWord_1620597).sum := by decide
  have hdescent : baseEnd_1620597 < baseStart_1620597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620612 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 2, 6]
def baseStart_1620612 : Nat := 118140960795 + 1620612 * 2 ^ 59
def prefixEnd_1620612 : Nat := 4983230072969 + 3 ^ 40 * 1620612 * 2
def baseEnd_1620612 : Nat := 277384303481439527265649

theorem tailTrace_1620612 : CollatzResearch.WordTrace tailWord_1620612 prefixEnd_1620612 277384303481439527265649 := by
  unfold tailWord_1620612
  simp only [CollatzResearch.WordTrace]
  refine ⟨29554287802403488669624045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39405717069871318226165393 29554287802403488669624045)
  ·
    refine ⟨11082857925901308251109017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29554287802403488669624045 11082857925901308251109017)
    ·
      refine ⟨8312143444425981188331763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11082857925901308251109017 8312143444425981188331763)
      ·
        refine ⟨12468215166638971782497645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8312143444425981188331763 12468215166638971782497645)
        ·
          refine ⟨4675580687489614418436617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12468215166638971782497645 4675580687489614418436617)
          ·
            refine ⟨3506685515617210813827463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4675580687489614418436617 3506685515617210813827463)
            ·
              refine ⟨5260028273425816220741195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3506685515617210813827463 5260028273425816220741195)
              ·
                refine ⟨7890042410138724331111793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5260028273425816220741195 7890042410138724331111793)
                ·
                  refine ⟨5917531807604043248333845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7890042410138724331111793 5917531807604043248333845)
                  ·
                    refine ⟨277384303481439527265649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5917531807604043248333845 277384303481439527265649)
                    ·
                      rfl

theorem cell23_1620612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_1620612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620612 prefixEnd_1620612 := by exact prefixLift 1620612
  have htrace : WordTrace (prefixWord ++ tailWord_1620612) baseStart_1620612 baseEnd_1620612 := by
    simpa [prefixWord, tailWord_1620612, baseEnd_1620612] using wordTrace_append hprefix tailTrace_1620612
  have hstable : (prefixWord ++ tailWord_1620612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620612).length < 2 ^ (prefixWord ++ tailWord_1620612).sum := by decide
  have hdescent : baseEnd_1620612 < baseStart_1620612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620622 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3]
def baseStart_1620622 : Nat := 118140960795 + 1620622 * 2 ^ 59
def prefixEnd_1620622 : Nat := 4983230072969 + 3 ^ 40 * 1620622 * 2
def baseEnd_1620622 : Nat := 832158045250863542671901

theorem tailTrace_1620622 : CollatzResearch.WordTrace tailWord_1620622 prefixEnd_1620622 832158045250863542671901 := by
  unfold tailWord_1620622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7388617541846343630889015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39405960223180499364741413 7388617541846343630889015)
  ·
    refine ⟨11082926312769515446333523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7388617541846343630889015 11082926312769515446333523)
    ·
      refine ⟨16624389469154273169500285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11082926312769515446333523 16624389469154273169500285)
      ·
        refine ⟨6234146050932852438562607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16624389469154273169500285 6234146050932852438562607)
        ·
          refine ⟨9351219076399278657843911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6234146050932852438562607 9351219076399278657843911)
          ·
            refine ⟨14026828614598917986765867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9351219076399278657843911 14026828614598917986765867)
            ·
              refine ⟨21040242921898376980148801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14026828614598917986765867 21040242921898376980148801)
              ·
                refine ⟨15780182191423782735111601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21040242921898376980148801 15780182191423782735111601)
                ·
                  refine ⟨11835136643567837051333701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15780182191423782735111601 11835136643567837051333701)
                  ·
                    refine ⟨2219088120668969447125069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11835136643567837051333701 2219088120668969447125069)
                    ·
                      refine ⟨832158045250863542671901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2219088120668969447125069 832158045250863542671901)
                      ·
                        rfl

theorem cell23_1620622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_1620622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620622 prefixEnd_1620622 := by exact prefixLift 1620622
  have htrace : WordTrace (prefixWord ++ tailWord_1620622) baseStart_1620622 baseEnd_1620622 := by
    simpa [prefixWord, tailWord_1620622, baseEnd_1620622] using wordTrace_append hprefix tailTrace_1620622
  have hstable : (prefixWord ++ tailWord_1620622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620622).length < 2 ^ (prefixWord ++ tailWord_1620622).sum := by decide
  have hdescent : baseEnd_1620622 < baseStart_1620622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620640 : List Nat := [2, 1, 1, 4, 5, 1, 2, 1, 1, 3, 2]
def baseStart_1620640 : Nat := 118140960795 + 1620640 * 2 ^ 59
def prefixEnd_1620640 : Nat := 4983230072969 + 3 ^ 40 * 1620640 * 2
def baseEnd_1620640 : Nat := 832167287902644472246819

theorem tailTrace_1620640 : CollatzResearch.WordTrace tailWord_1620640 prefixEnd_1620640 832167287902644472246819 := by
  unfold tailWord_1620640
  simp only [CollatzResearch.WordTrace]
  refine ⟨29554798424352769060633687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39406397899137025414178249 29554798424352769060633687)
  ·
    refine ⟨44332197636529153590950531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29554798424352769060633687 44332197636529153590950531)
    ·
      refine ⟨66498296454793730386425797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44332197636529153590950531 66498296454793730386425797)
      ·
        refine ⟨12468430585273824447454837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66498296454793730386425797 12468430585273824447454837)
        ·
          refine ⟨1168915367369421041948891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12468430585273824447454837 1168915367369421041948891)
          ·
            refine ⟨1753373051054131562923337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168915367369421041948891 1753373051054131562923337)
            ·
              refine ⟨1315029788290598672192503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1753373051054131562923337 1315029788290598672192503)
              ·
                refine ⟨1972544682435898008288755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315029788290598672192503 1972544682435898008288755)
                ·
                  refine ⟨2958817023653847012433133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1972544682435898008288755 2958817023653847012433133)
                  ·
                    refine ⟨1109556383870192629662425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2958817023653847012433133 1109556383870192629662425)
                    ·
                      refine ⟨832167287902644472246819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1109556383870192629662425 832167287902644472246819)
                      ·
                        rfl

theorem cell23_1620640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_1620640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620640 prefixEnd_1620640 := by exact prefixLift 1620640
  have htrace : WordTrace (prefixWord ++ tailWord_1620640) baseStart_1620640 baseEnd_1620640 := by
    simpa [prefixWord, tailWord_1620640, baseEnd_1620640] using wordTrace_append hprefix tailTrace_1620640
  have hstable : (prefixWord ++ tailWord_1620640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620640).length < 2 ^ (prefixWord ++ tailWord_1620640).sum := by decide
  have hdescent : baseEnd_1620640 < baseStart_1620640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620653 : List Nat := [1, 5, 2, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_1620653 : Nat := 118140960795 + 1620653 * 2 ^ 59
def prefixEnd_1620653 : Nat := 4983230072969 + 3 ^ 40 * 1620653 * 2
def baseEnd_1620653 : Nat := 832173963151152921384259

theorem tailTrace_1620653 : CollatzResearch.WordTrace tailWord_1620653 prefixEnd_1620653 832173963151152921384259 := by
  unfold tailWord_1620653
  simp only [CollatzResearch.WordTrace]
  refine ⟨59110070997658441341490613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39406713998438960894327075 59110070997658441341490613)
  ·
    refine ⟨5541569156030478875764745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59110070997658441341490613 5541569156030478875764745)
    ·
      refine ⟨4156176867022859156823559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5541569156030478875764745 4156176867022859156823559)
      ·
        refine ⟨6234265300534288735235339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4156176867022859156823559 6234265300534288735235339)
        ·
          refine ⟨9351397950801433102853009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6234265300534288735235339 9351397950801433102853009)
          ·
            refine ⟨7013548463101074827139757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9351397950801433102853009 7013548463101074827139757)
            ·
              refine ⟨2630080673662903060177409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7013548463101074827139757 2630080673662903060177409)
              ·
                refine ⟨1972560505247177295133057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2630080673662903060177409 1972560505247177295133057)
                ·
                  refine ⟨1479420378935382971349793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1972560505247177295133057 1479420378935382971349793)
                  ·
                    refine ⟨1109565284201537228512345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1479420378935382971349793 1109565284201537228512345)
                    ·
                      refine ⟨832173963151152921384259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1109565284201537228512345 832173963151152921384259)
                      ·
                        rfl

theorem cell23_1620653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_1620653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620653 prefixEnd_1620653 := by exact prefixLift 1620653
  have htrace : WordTrace (prefixWord ++ tailWord_1620653) baseStart_1620653 baseEnd_1620653 := by
    simpa [prefixWord, tailWord_1620653, baseEnd_1620653] using wordTrace_append hprefix tailTrace_1620653
  have hstable : (prefixWord ++ tailWord_1620653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620653).length < 2 ^ (prefixWord ++ tailWord_1620653).sum := by decide
  have hdescent : baseEnd_1620653 < baseStart_1620653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620665 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1620665 : Nat := 118140960795 + 1620665 * 2 ^ 59
def prefixEnd_1620665 : Nat := 4983230072969 + 3 ^ 40 * 1620665 * 2
def baseEnd_1620665 : Nat := 832180124919006874434203

theorem tailTrace_1620665 : CollatzResearch.WordTrace tailWord_1620665 prefixEnd_1620665 832180124919006874434203 := by
  unfold tailWord_1620665
  simp only [CollatzResearch.WordTrace]
  refine ⟨59110508673614967390927449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39407005782409978260618299 59110508673614967390927449)
  ·
    refine ⟨44332881505211225543195587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59110508673614967390927449 44332881505211225543195587)
    ·
      refine ⟨66499322257816838314793381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44332881505211225543195587 66499322257816838314793381)
      ·
        refine ⟨12468622923340657184023759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66499322257816838314793381 12468622923340657184023759)
        ·
          refine ⟨18702934385010985776035639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12468622923340657184023759 18702934385010985776035639)
          ·
            refine ⟨28054401577516478664053459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18702934385010985776035639 28054401577516478664053459)
            ·
              refine ⟨42081602366274717996080189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28054401577516478664053459 42081602366274717996080189)
              ·
                refine ⟨15780600887353019248530071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42081602366274717996080189 15780600887353019248530071)
                ·
                  refine ⟨23670901331029528872795107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15780600887353019248530071 23670901331029528872795107)
                  ·
                    refine ⟨35506351996544293309192661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23670901331029528872795107 35506351996544293309192661)
                    ·
                      refine ⟨832180124919006874434203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35506351996544293309192661 832180124919006874434203)
                      ·
                        rfl

theorem cell23_1620665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1620665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620665 prefixEnd_1620665 := by exact prefixLift 1620665
  have htrace : WordTrace (prefixWord ++ tailWord_1620665) baseStart_1620665 baseEnd_1620665 := by
    simpa [prefixWord, tailWord_1620665, baseEnd_1620665] using wordTrace_append hprefix tailTrace_1620665
  have hstable : (prefixWord ++ tailWord_1620665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620665).length < 2 ^ (prefixWord ++ tailWord_1620665).sum := by decide
  have hdescent : baseEnd_1620665 < baseStart_1620665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620693 : List Nat := [1, 3, 2, 5, 1, 2, 1, 3, 5]
def baseStart_1620693 : Nat := 118140960795 + 1620693 * 2 ^ 59
def prefixEnd_1620693 : Nat := 4983230072969 + 3 ^ 40 * 1620693 * 2
def baseEnd_1620693 : Nat := 92466055819703640542675

theorem tailTrace_1620693 : CollatzResearch.WordTrace tailWord_1620693 prefixEnd_1620693 92466055819703640542675 := by
  unfold tailWord_1620693
  simp only [CollatzResearch.WordTrace]
  refine ⟨59111529917513528172946733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39407686611675685448631155 59111529917513528172946733)
  ·
    refine ⟨22166823719067573064855025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59111529917513528172946733 22166823719067573064855025)
    ·
      refine ⟨16625117789300679798641269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22166823719067573064855025 16625117789300679798641269)
      ·
        refine ⟨1558604792746938731122619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16625117789300679798641269 1558604792746938731122619)
        ·
          refine ⟨2337907189120408096683929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558604792746938731122619 2337907189120408096683929)
          ·
            refine ⟨1753430391840306072512947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2337907189120408096683929 1753430391840306072512947)
            ·
              refine ⟨2630145587760459108769421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753430391840306072512947 2630145587760459108769421)
              ·
                refine ⟨986304595410172165788533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2630145587760459108769421 986304595410172165788533)
                ·
                  refine ⟨92466055819703640542675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 986304595410172165788533 92466055819703640542675)
                  ·
                    rfl

theorem cell23_1620693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 5].length) (baseStart_1620693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620693 prefixEnd_1620693 := by exact prefixLift 1620693
  have htrace : WordTrace (prefixWord ++ tailWord_1620693) baseStart_1620693 baseEnd_1620693 := by
    simpa [prefixWord, tailWord_1620693, baseEnd_1620693] using wordTrace_append hprefix tailTrace_1620693
  have hstable : (prefixWord ++ tailWord_1620693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620693).length < 2 ^ (prefixWord ++ tailWord_1620693).sum := by decide
  have hdescent : baseEnd_1620693 < baseStart_1620693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620709 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1620709 : Nat := 118140960795 + 1620709 * 2 ^ 59
def prefixEnd_1620709 : Nat := 4983230072969 + 3 ^ 40 * 1620709 * 2
def baseEnd_1620709 : Nat := 832202718067804702284001

theorem tailTrace_1620709 : CollatzResearch.WordTrace tailWord_1620709 prefixEnd_1620709 832202718067804702284001 := by
  unfold tailWord_1620709
  simp only [CollatzResearch.WordTrace]
  refine ⟨59112113485455562905529181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39408075656970375270352787 59112113485455562905529181)
  ·
    refine ⟨22167042557045836089573443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59112113485455562905529181 22167042557045836089573443)
    ·
      refine ⟨33250563835568754134360165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22167042557045836089573443 33250563835568754134360165)
      ·
        refine ⟨6234480719169141400192531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33250563835568754134360165 6234480719169141400192531)
        ·
          refine ⟨9351721078753712100288797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6234480719169141400192531 9351721078753712100288797)
          ·
            refine ⟨3506895404532642037608299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9351721078753712100288797 3506895404532642037608299)
            ·
              refine ⟨5260343106798963056412449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3506895404532642037608299 5260343106798963056412449)
              ·
                refine ⟨3945257330099222292309337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5260343106798963056412449 3945257330099222292309337)
                ·
                  refine ⟨2958942997574416719232003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3945257330099222292309337 2958942997574416719232003)
                  ·
                    refine ⟨4438414496361625078848005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2958942997574416719232003 4438414496361625078848005)
                    ·
                      refine ⟨832202718067804702284001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4438414496361625078848005 832202718067804702284001)
                      ·
                        rfl

theorem cell23_1620709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1620709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620709 prefixEnd_1620709 := by exact prefixLift 1620709
  have htrace : WordTrace (prefixWord ++ tailWord_1620709) baseStart_1620709 baseEnd_1620709 := by
    simpa [prefixWord, tailWord_1620709, baseEnd_1620709] using wordTrace_append hprefix tailTrace_1620709
  have hstable : (prefixWord ++ tailWord_1620709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620709).length < 2 ^ (prefixWord ++ tailWord_1620709).sum := by decide
  have hdescent : baseEnd_1620709 < baseStart_1620709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620719 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 3, 4]
def baseStart_1620719 : Nat := 118140960795 + 1620719 * 2 ^ 59
def prefixEnd_1620719 : Nat := 4983230072969 + 3 ^ 40 * 1620719 * 2
def baseEnd_1620719 : Nat := 277402617624783221052985

theorem tailTrace_1620719 : CollatzResearch.WordTrace tailWord_1620719 prefixEnd_1620719 277402617624783221052985 := by
  unfold tailWord_1620719
  simp only [CollatzResearch.WordTrace]
  refine ⟨59112478215419334613393211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39408318810279556408928807 59112478215419334613393211)
  ·
    refine ⟨88668717323129001920089817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59112478215419334613393211 88668717323129001920089817)
    ·
      refine ⟨66501537992346751440067363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88668717323129001920089817 66501537992346751440067363)
      ·
        refine ⟨99752306988520127160101045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66501537992346751440067363 99752306988520127160101045)
        ·
          refine ⟨9351778780173761921259473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99752306988520127160101045 9351778780173761921259473)
          ·
            refine ⟨7013834085130321440944605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9351778780173761921259473 7013834085130321440944605)
            ·
              refine ⟨2630187781923870540354227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7013834085130321440944605 2630187781923870540354227)
              ·
                refine ⟨3945281672885805810531341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2630187781923870540354227 3945281672885805810531341)
                ·
                  refine ⟨1479480627332177178949253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3945281672885805810531341 1479480627332177178949253)
                  ·
                    refine ⟨277402617624783221052985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1479480627332177178949253 277402617624783221052985)
                    ·
                      rfl

theorem cell23_1620719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 4].length) (baseStart_1620719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620719 prefixEnd_1620719 := by exact prefixLift 1620719
  have htrace : WordTrace (prefixWord ++ tailWord_1620719) baseStart_1620719 baseEnd_1620719 := by
    simpa [prefixWord, tailWord_1620719, baseEnd_1620719] using wordTrace_append hprefix tailTrace_1620719
  have hstable : (prefixWord ++ tailWord_1620719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620719).length < 2 ^ (prefixWord ++ tailWord_1620719).sum := by decide
  have hdescent : baseEnd_1620719 < baseStart_1620719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620770 : List Nat := [3, 3, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_1620770 : Nat := 118140960795 + 1620770 * 2 ^ 59
def prefixEnd_1620770 : Nat := 4983230072969 + 3 ^ 40 * 1620770 * 2
def baseEnd_1620770 : Nat := 277411346795909654540407

theorem tailTrace_1620770 : CollatzResearch.WordTrace tailWord_1620770 prefixEnd_1620770 277411346795909654540407 := by
  unfold tailWord_1620770
  simp only [CollatzResearch.WordTrace]
  refine ⟨14778584584558642580874941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39409558892156380215666509 14778584584558642580874941)
  ·
    refine ⟨5541969219209490967828103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14778584584558642580874941 5541969219209490967828103)
    ·
      refine ⟨8312953828814236451742155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5541969219209490967828103 8312953828814236451742155)
      ·
        refine ⟨12469430743221354677613233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8312953828814236451742155 12469430743221354677613233)
        ·
          refine ⟨9352073057416016008209925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12469430743221354677613233 9352073057416016008209925)
          ·
            refine ⟨1753513698265503001539361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9352073057416016008209925 1753513698265503001539361)
            ·
              refine ⟨1315135273699127251154521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1753513698265503001539361 1315135273699127251154521)
              ·
                refine ⟨986351455274345438365891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1315135273699127251154521 986351455274345438365891)
                ·
                  refine ⟨1479527182911518157548837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986351455274345438365891 1479527182911518157548837)
                  ·
                    refine ⟨277411346795909654540407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1479527182911518157548837 277411346795909654540407)
                    ·
                      rfl

theorem cell23_1620770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_1620770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620770 prefixEnd_1620770 := by exact prefixLift 1620770
  have htrace : WordTrace (prefixWord ++ tailWord_1620770) baseStart_1620770 baseEnd_1620770 := by
    simpa [prefixWord, tailWord_1620770, baseEnd_1620770] using wordTrace_append hprefix tailTrace_1620770
  have hstable : (prefixWord ++ tailWord_1620770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620770).length < 2 ^ (prefixWord ++ tailWord_1620770).sum := by decide
  have hdescent : baseEnd_1620770 < baseStart_1620770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620776 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_1620776 : Nat := 118140960795 + 1620776 * 2 ^ 59
def prefixEnd_1620776 : Nat := 4983230072969 + 3 ^ 40 * 1620776 * 2
def baseEnd_1620776 : Nat := 832237121271655940146193

theorem tailTrace_1620776 : CollatzResearch.WordTrace tailWord_1620776 prefixEnd_1620776 832237121271655940146193 := by
  unfold tailWord_1620776
  simp only [CollatzResearch.WordTrace]
  refine ⟨29557278588106416674109091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39409704784141888898812121 29557278588106416674109091)
  ·
    refine ⟨44335917882159625011163637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29557278588106416674109091 44335917882159625011163637)
    ·
      refine ⟨4156492301452464844796591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44335917882159625011163637 4156492301452464844796591)
      ·
        refine ⟨6234738452178697267194887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4156492301452464844796591 6234738452178697267194887)
        ·
          refine ⟨9352107678268045900792331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6234738452178697267194887 9352107678268045900792331)
          ·
            refine ⟨14028161517402068851188497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9352107678268045900792331 14028161517402068851188497)
            ·
              refine ⟨10521121138051551638391373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14028161517402068851188497 10521121138051551638391373)
              ·
                refine ⟨3945420426769331864396765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10521121138051551638391373 3945420426769331864396765)
                ·
                  refine ⟨1479532660038499449148787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3945420426769331864396765 1479532660038499449148787)
                  ·
                    refine ⟨2219298990057749173723181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1479532660038499449148787 2219298990057749173723181)
                    ·
                      refine ⟨832237121271655940146193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2219298990057749173723181 832237121271655940146193)
                      ·
                        rfl

theorem cell23_1620776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_1620776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620776 prefixEnd_1620776 := by exact prefixLift 1620776
  have htrace : WordTrace (prefixWord ++ tailWord_1620776) baseStart_1620776 baseEnd_1620776 := by
    simpa [prefixWord, tailWord_1620776, baseEnd_1620776] using wordTrace_append hprefix tailTrace_1620776
  have hstable : (prefixWord ++ tailWord_1620776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620776).length < 2 ^ (prefixWord ++ tailWord_1620776).sum := by decide
  have hdescent : baseEnd_1620776 < baseStart_1620776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620799 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 4]
def baseStart_1620799 : Nat := 118140960795 + 1620799 * 2 ^ 59
def prefixEnd_1620799 : Nat := 4983230072969 + 3 ^ 40 * 1620799 * 2
def baseEnd_1620799 : Nat := 832248931326709350158587

theorem tailTrace_1620799 : CollatzResearch.WordTrace tailWord_1620799 prefixEnd_1620799 832248931326709350158587 := by
  unfold tailWord_1620799
  simp only [CollatzResearch.WordTrace]
  refine ⟨59115396055129508276305451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39410264036753005517536967 59115396055129508276305451)
  ·
    refine ⟨88673094082694262414458177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59115396055129508276305451 88673094082694262414458177)
    ·
      refine ⟨66504820562020696810843633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88673094082694262414458177 66504820562020696810843633)
      ·
        refine ⟨49878615421515522608132725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66504820562020696810843633 49878615421515522608132725)
        ·
          refine ⟨4676120195767080244512443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49878615421515522608132725 4676120195767080244512443)
          ·
            refine ⟨7014180293650620366768665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4676120195767080244512443 7014180293650620366768665)
            ·
              refine ⟨5260635220237965275076499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7014180293650620366768665 5260635220237965275076499)
              ·
                refine ⟨7890952830356947912614749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5260635220237965275076499 7890952830356947912614749)
                ·
                  refine ⟨2959107311383855467230531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7890952830356947912614749 2959107311383855467230531)
                  ·
                    refine ⟨4438660967075783200845797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2959107311383855467230531 4438660967075783200845797)
                    ·
                      refine ⟨832248931326709350158587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4438660967075783200845797 832248931326709350158587)
                      ·
                        rfl

theorem cell23_1620799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_1620799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620799 prefixEnd_1620799 := by exact prefixLift 1620799
  have htrace : WordTrace (prefixWord ++ tailWord_1620799) baseStart_1620799 baseEnd_1620799 := by
    simpa [prefixWord, tailWord_1620799, baseEnd_1620799] using wordTrace_append hprefix tailTrace_1620799
  have hstable : (prefixWord ++ tailWord_1620799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620799).length < 2 ^ (prefixWord ++ tailWord_1620799).sum := by decide
  have hdescent : baseEnd_1620799 < baseStart_1620799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620813 : List Nat := [1, 6, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_1620813 : Nat := 118140960795 + 1620813 * 2 ^ 59
def prefixEnd_1620813 : Nat := 4983230072969 + 3 ^ 40 * 1620813 * 2
def baseEnd_1620813 : Nat := 277418706685290765127841

theorem tailTrace_1620813 : CollatzResearch.WordTrace tailWord_1620813 prefixEnd_1620813 277418706685290765127841 := by
  unfold tailWord_1620813
  simp only [CollatzResearch.WordTrace]
  refine ⟨59115906677078788667315093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39410604451385859111543395 59115906677078788667315093)
  ·
    refine ⟨2771058125488068218780395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59115906677078788667315093 2771058125488068218780395)
    ·
      refine ⟨4156587188232102328170593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2771058125488068218780395 4156587188232102328170593)
      ·
        refine ⟨3117440391174076746127945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4156587188232102328170593 3117440391174076746127945)
        ·
          refine ⟨2338080293380557559595959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3117440391174076746127945 2338080293380557559595959)
          ·
            refine ⟨3507120440070836339393939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338080293380557559595959 3507120440070836339393939)
            ·
              refine ⟨5260680660106254509090909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3507120440070836339393939 5260680660106254509090909)
              ·
                refine ⟨1972755247539845440909091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5260680660106254509090909 1972755247539845440909091)
                ·
                  refine ⟨2959132871309768161363637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1972755247539845440909091 2959132871309768161363637)
                  ·
                    refine ⟨277418706685290765127841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2959132871309768161363637 277418706685290765127841)
                    ·
                      rfl

theorem cell23_1620813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_1620813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620813 prefixEnd_1620813 := by exact prefixLift 1620813
  have htrace : WordTrace (prefixWord ++ tailWord_1620813) baseStart_1620813 baseEnd_1620813 := by
    simpa [prefixWord, tailWord_1620813, baseEnd_1620813] using wordTrace_append hprefix tailTrace_1620813
  have hstable : (prefixWord ++ tailWord_1620813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620813).length < 2 ^ (prefixWord ++ tailWord_1620813).sum := by decide
  have hdescent : baseEnd_1620813 < baseStart_1620813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620816 : List Nat := [2, 1, 1, 1, 1, 4, 6, 1, 1, 1, 4]
def baseStart_1620816 : Nat := 118140960795 + 1620816 * 2 ^ 59
def prefixEnd_1620816 : Nat := 4983230072969 + 3 ^ 40 * 1620816 * 2
def baseEnd_1620816 : Nat := 832257660497835783646009

theorem tailTrace_1620816 : CollatzResearch.WordTrace tailWord_1620816 prefixEnd_1620816 832257660497835783646009 := by
  unfold tailWord_1620816
  simp only [CollatzResearch.WordTrace]
  refine ⟨29558008048033960089837151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39410677397378613453116201 29558008048033960089837151)
  ·
    refine ⟨44337012072050940134755727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29558008048033960089837151 44337012072050940134755727)
    ·
      refine ⟨66505518108076410202133591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44337012072050940134755727 66505518108076410202133591)
      ·
        refine ⟨99758277162114615303200387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66505518108076410202133591 99758277162114615303200387)
        ·
          refine ⟨149637415743171922954800581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99758277162114615303200387 149637415743171922954800581)
          ·
            refine ⟨28057015451844735554025109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149637415743171922954800581 28057015451844735554025109)
            ·
              refine ⟨1315172599305221979094927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28057015451844735554025109 1315172599305221979094927)
              ·
                refine ⟨1972758898957832968642391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315172599305221979094927 1972758898957832968642391)
                ·
                  refine ⟨2959138348436749452963587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1972758898957832968642391 2959138348436749452963587)
                  ·
                    refine ⟨4438707522655124179445381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2959138348436749452963587 4438707522655124179445381)
                    ·
                      refine ⟨832257660497835783646009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4438707522655124179445381 832257660497835783646009)
                      ·
                        rfl

theorem cell23_1620816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 1, 1, 4].length) (baseStart_1620816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620816 prefixEnd_1620816 := by exact prefixLift 1620816
  have htrace : WordTrace (prefixWord ++ tailWord_1620816) baseStart_1620816 baseEnd_1620816 := by
    simpa [prefixWord, tailWord_1620816, baseEnd_1620816] using wordTrace_append hprefix tailTrace_1620816
  have hstable : (prefixWord ++ tailWord_1620816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620816).length < 2 ^ (prefixWord ++ tailWord_1620816).sum := by decide
  have hdescent : baseEnd_1620816 < baseStart_1620816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620826 : List Nat := [3, 1, 1, 2, 1, 4, 3, 2, 2, 4]
def baseStart_1620826 : Nat := 118140960795 + 1620826 * 2 ^ 59
def prefixEnd_1620826 : Nat := 4983230072969 + 3 ^ 40 * 1620826 * 2
def baseEnd_1620826 : Nat := 277420931768126914840321

theorem tailTrace_1620826 : CollatzResearch.WordTrace tailWord_1620826 prefixEnd_1620826 277420931768126914840321 := by
  unfold tailWord_1620826
  simp only [CollatzResearch.WordTrace]
  refine ⟨14779095206507922971884583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39410920550687794591692221 14779095206507922971884583)
  ·
    refine ⟨22168642809761884457826875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14779095206507922971884583 22168642809761884457826875)
    ·
      refine ⟨33252964214642826686740313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22168642809761884457826875 33252964214642826686740313)
      ·
        refine ⟨24939723160982120015055235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33252964214642826686740313 24939723160982120015055235)
        ·
          refine ⟨37409584741473180022582853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24939723160982120015055235 37409584741473180022582853)
          ·
            refine ⟨7014297139026221254234285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37409584741473180022582853 7014297139026221254234285)
            ·
              refine ⟨2630361427134832970337857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7014297139026221254234285 2630361427134832970337857)
              ·
                refine ⟨1972771070351124727753393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2630361427134832970337857 1972771070351124727753393)
                ·
                  refine ⟨1479578302763343545815045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1972771070351124727753393 1479578302763343545815045)
                  ·
                    refine ⟨277420931768126914840321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1479578302763343545815045 277420931768126914840321)
                    ·
                      rfl

theorem cell23_1620826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_1620826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620826 prefixEnd_1620826 := by exact prefixLift 1620826
  have htrace : WordTrace (prefixWord ++ tailWord_1620826) baseStart_1620826 baseEnd_1620826 := by
    simpa [prefixWord, tailWord_1620826, baseEnd_1620826] using wordTrace_append hprefix tailTrace_1620826
  have hstable : (prefixWord ++ tailWord_1620826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620826).length < 2 ^ (prefixWord ++ tailWord_1620826).sum := by decide
  have hdescent : baseEnd_1620826 < baseStart_1620826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620846 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_1620846 : Nat := 118140960795 + 1620846 * 2 ^ 59
def prefixEnd_1620846 : Nat := 4983230072969 + 3 ^ 40 * 1620846 * 2
def baseEnd_1620846 : Nat := 832273064917470666270871

theorem tailTrace_1620846 : CollatzResearch.WordTrace tailWord_1620846 prefixEnd_1620846 832273064917470666270871 := by
  unfold tailWord_1620846
  simp only [CollatzResearch.WordTrace]
  refine ⟨7389638785744904412908299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39411406857306156868844261 7389638785744904412908299)
  ·
    refine ⟨11084458178617356619362449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7389638785744904412908299 11084458178617356619362449)
    ·
      refine ⟨8313343633963017464521837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11084458178617356619362449 8313343633963017464521837)
      ·
        refine ⟨3117503862736131549195689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8313343633963017464521837 3117503862736131549195689)
        ·
          refine ⟨2338127897052098661896767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3117503862736131549195689 2338127897052098661896767)
          ·
            refine ⟨3507191845578147992845151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338127897052098661896767 3507191845578147992845151)
            ·
              refine ⟨5260787768367221989267727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3507191845578147992845151 5260787768367221989267727)
              ·
                refine ⟨7891181652550832983901591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5260787768367221989267727 7891181652550832983901591)
                ·
                  refine ⟨11836772478826249475852387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7891181652550832983901591 11836772478826249475852387)
                  ·
                    refine ⟨17755158718239374213778581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11836772478826249475852387 17755158718239374213778581)
                    ·
                      refine ⟨832273064917470666270871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17755158718239374213778581 832273064917470666270871)
                      ·
                        rfl

theorem cell23_1620846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_1620846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620846 prefixEnd_1620846 := by exact prefixLift 1620846
  have htrace : WordTrace (prefixWord ++ tailWord_1620846) baseStart_1620846 baseEnd_1620846 := by
    simpa [prefixWord, tailWord_1620846, baseEnd_1620846] using wordTrace_append hprefix tailTrace_1620846
  have hstable : (prefixWord ++ tailWord_1620846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620846).length < 2 ^ (prefixWord ++ tailWord_1620846).sum := by decide
  have hdescent : baseEnd_1620846 < baseStart_1620846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620853 : List Nat := [1, 3, 4, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_1620853 : Nat := 118140960795 + 1620853 * 2 ^ 59
def prefixEnd_1620853 : Nat := 4983230072969 + 3 ^ 40 * 1620853 * 2
def baseEnd_1620853 : Nat := 832276659282052138883339

theorem tailTrace_1620853 : CollatzResearch.WordTrace tailWord_1620853 prefixEnd_1620853 832276659282052138883339 := by
  unfold tailWord_1620853
  simp only [CollatzResearch.WordTrace]
  refine ⟨59117365596933875498771213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39411577064622583665847475 59117365596933875498771213)
  ·
    refine ⟨22169012098850203312039205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59117365596933875498771213 22169012098850203312039205)
    ·
      refine ⟨4156689768534413121007351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22169012098850203312039205 4156689768534413121007351)
      ·
        refine ⟨6235034652801619681511027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4156689768534413121007351 6235034652801619681511027)
        ·
          refine ⟨9352551979202429522266541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6235034652801619681511027 9352551979202429522266541)
          ·
            refine ⟨3507206992200911070849953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9352551979202429522266541 3507206992200911070849953)
            ·
              refine ⟨2630405244150683303137465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3507206992200911070849953 2630405244150683303137465)
              ·
                refine ⟨1972803933113012477353099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2630405244150683303137465 1972803933113012477353099)
                ·
                  refine ⟨2959205899669518716029649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1972803933113012477353099 2959205899669518716029649)
                  ·
                    refine ⟨2219404424752139037022237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2959205899669518716029649 2219404424752139037022237)
                    ·
                      refine ⟨832276659282052138883339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2219404424752139037022237 832276659282052138883339)
                      ·
                        rfl

theorem cell23_1620853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_1620853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620853 prefixEnd_1620853 := by exact prefixLift 1620853
  have htrace : WordTrace (prefixWord ++ tailWord_1620853) baseStart_1620853 baseEnd_1620853 := by
    simpa [prefixWord, tailWord_1620853, baseEnd_1620853] using wordTrace_append hprefix tailTrace_1620853
  have hstable : (prefixWord ++ tailWord_1620853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620853).length < 2 ^ (prefixWord ++ tailWord_1620853).sum := by decide
  have hdescent : baseEnd_1620853 < baseStart_1620853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620940 : List Nat := [2, 2, 1, 4, 1, 1, 4, 2, 2, 2, 2]
def baseStart_1620940 : Nat := 118140960795 + 1620940 * 2 ^ 59
def prefixEnd_1620940 : Nat := 4983230072969 + 3 ^ 40 * 1620940 * 2
def baseEnd_1620940 : Nat := 832321332098993298495439

theorem tailTrace_1620940 : CollatzResearch.WordTrace tailWord_1620940 prefixEnd_1620940 832321332098993298495439 := by
  unfold tailWord_1620940
  simp only [CollatzResearch.WordTrace]
  refine ⟨29560269373809344678594137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39413692498412459571458849 29560269373809344678594137)
  ·
    refine ⟨22170202030357008508945603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29560269373809344678594137 22170202030357008508945603)
    ·
      refine ⟨33255303045535512763418405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22170202030357008508945603 33255303045535512763418405)
      ·
        refine ⟨6235369321037908643140951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33255303045535512763418405 6235369321037908643140951)
        ·
          refine ⟨9353053981556862964711427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6235369321037908643140951 9353053981556862964711427)
          ·
            refine ⟨14029580972335294447067141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9353053981556862964711427 14029580972335294447067141)
            ·
              refine ⟨2630546432312867708825089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14029580972335294447067141 2630546432312867708825089)
              ·
                refine ⟨1972909824234650781618817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2630546432312867708825089 1972909824234650781618817)
                ·
                  refine ⟨1479682368175988086214113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1972909824234650781618817 1479682368175988086214113)
                  ·
                    refine ⟨1109761776131991064660585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1479682368175988086214113 1109761776131991064660585)
                    ·
                      refine ⟨832321332098993298495439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1109761776131991064660585 832321332098993298495439)
                      ·
                        rfl

theorem cell23_1620940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_1620940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1620940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1620940 prefixEnd_1620940 := by exact prefixLift 1620940
  have htrace : WordTrace (prefixWord ++ tailWord_1620940) baseStart_1620940 baseEnd_1620940 := by
    simpa [prefixWord, tailWord_1620940, baseEnd_1620940] using wordTrace_append hprefix tailTrace_1620940
  have hstable : (prefixWord ++ tailWord_1620940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620940).length < 2 ^ (prefixWord ++ tailWord_1620940).sum := by decide
  have hdescent : baseEnd_1620940 < baseStart_1620940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621013 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 2, 4, 2]
def baseStart_1621013 : Nat := 118140960795 + 1621013 * 2 ^ 59
def prefixEnd_1621013 : Nat := 4983230072969 + 3 ^ 40 * 1621013 * 2
def baseEnd_1621013 : Nat := 832358816186771512882603

theorem tailTrace_1621013 : CollatzResearch.WordTrace tailWord_1621013 prefixEnd_1621013 832358816186771512882603 := by
  unfold tailWord_1621013
  simp only [CollatzResearch.WordTrace]
  refine ⟨59123201276354222824595693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39415467517569481883063795 59123201276354222824595693)
  ·
    refine ⟨22171200478632833559223385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59123201276354222824595693 22171200478632833559223385)
    ·
      refine ⟨16628400358974625169417539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22171200478632833559223385 16628400358974625169417539)
      ·
        refine ⟨24942600538461937754126309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16628400358974625169417539 24942600538461937754126309)
        ·
          refine ⟨4676737600961613328898683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24942600538461937754126309 4676737600961613328898683)
          ·
            refine ⟨7015106401442419993348025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4676737600961613328898683 7015106401442419993348025)
            ·
              refine ⟨5261329801081814995011019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7015106401442419993348025 5261329801081814995011019)
              ·
                refine ⟨7891994701622722492516529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5261329801081814995011019 7891994701622722492516529)
                ·
                  refine ⟨5918996026217041869387397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7891994701622722492516529 5918996026217041869387397)
                  ·
                    refine ⟨1109811754915695350510137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5918996026217041869387397 1109811754915695350510137)
                    ·
                      refine ⟨832358816186771512882603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1109811754915695350510137 832358816186771512882603)
                      ·
                        rfl

theorem cell23_1621013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_1621013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621013 prefixEnd_1621013 := by exact prefixLift 1621013
  have htrace : WordTrace (prefixWord ++ tailWord_1621013) baseStart_1621013 baseEnd_1621013 := by
    simpa [prefixWord, tailWord_1621013, baseEnd_1621013] using wordTrace_append hprefix tailTrace_1621013
  have hstable : (prefixWord ++ tailWord_1621013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621013).length < 2 ^ (prefixWord ++ tailWord_1621013).sum := by decide
  have hdescent : baseEnd_1621013 < baseStart_1621013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621016 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 1, 4, 3]
def baseStart_1621016 : Nat := 118140960795 + 1621016 * 2 ^ 59
def prefixEnd_1621016 : Nat := 4983230072969 + 3 ^ 40 * 1621016 * 2
def baseEnd_1621016 : Nat := 832360356628735001145089

theorem tailTrace_1621016 : CollatzResearch.WordTrace tailWord_1621016 prefixEnd_1621016 832360356628735001145089 := by
  unfold tailWord_1621016
  simp only [CollatzResearch.WordTrace]
  refine ⟨29561655347671677168477451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39415540463562236224636601 29561655347671677168477451)
  ·
    refine ⟨44342483021507515752716177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29561655347671677168477451 44342483021507515752716177)
    ·
      refine ⟨33256862266130636814537133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44342483021507515752716177 33256862266130636814537133)
      ·
        refine ⟨12471323349798988805451425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33256862266130636814537133 12471323349798988805451425)
        ·
          refine ⟨9353492512349241604088569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12471323349798988805451425 9353492512349241604088569)
          ·
            refine ⟨7015119384261931203066427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9353492512349241604088569 7015119384261931203066427)
            ·
              refine ⟨10522679076392896804599641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7015119384261931203066427 10522679076392896804599641)
              ·
                refine ⟨7892009307294672603449731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10522679076392896804599641 7892009307294672603449731)
                ·
                  refine ⟨11838013960942008905174597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7892009307294672603449731 11838013960942008905174597)
                  ·
                    refine ⟨2219627617676626669720237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11838013960942008905174597 2219627617676626669720237)
                    ·
                      refine ⟨832360356628735001145089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2219627617676626669720237 832360356628735001145089)
                      ·
                        rfl

theorem cell23_1621016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_1621016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621016 prefixEnd_1621016 := by exact prefixLift 1621016
  have htrace : WordTrace (prefixWord ++ tailWord_1621016) baseStart_1621016 baseEnd_1621016 := by
    simpa [prefixWord, tailWord_1621016, baseEnd_1621016] using wordTrace_append hprefix tailTrace_1621016
  have hstable : (prefixWord ++ tailWord_1621016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621016).length < 2 ^ (prefixWord ++ tailWord_1621016).sum := by decide
  have hdescent : baseEnd_1621016 < baseStart_1621016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621057 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 3, 4]
def baseStart_1621057 : Nat := 118140960795 + 1621057 * 2 ^ 59
def prefixEnd_1621057 : Nat := 4983230072969 + 3 ^ 40 * 1621057 * 2
def baseEnd_1621057 : Nat := 277460469778523113577467

theorem tailTrace_1621057 : CollatzResearch.WordTrace tailWord_1621057 prefixEnd_1621057 277460469778523113577467 := by
  unfold tailWord_1621057
  simp only [CollatzResearch.WordTrace]
  refine ⟨59124806088194818339197425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39416537392129878892798283 59124806088194818339197425)
  ·
    refine ⟨44343604566146113754398069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59124806088194818339197425 44343604566146113754398069)
    ·
      refine ⟨4157212928076198164474819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44343604566146113754398069 4157212928076198164474819)
      ·
        refine ⟨6235819392114297246712229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4157212928076198164474819 6235819392114297246712229)
        ·
          refine ⟨1169216136021430733758543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6235819392114297246712229 1169216136021430733758543)
          ·
            refine ⟨1753824204032146100637815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169216136021430733758543 1753824204032146100637815)
            ·
              refine ⟨2630736306048219150956723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753824204032146100637815 2630736306048219150956723)
              ·
                refine ⟨3946104459072328726435085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2630736306048219150956723 3946104459072328726435085)
                ·
                  refine ⟨1479789172152123272413157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3946104459072328726435085 1479789172152123272413157)
                  ·
                    refine ⟨277460469778523113577467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1479789172152123272413157 277460469778523113577467)
                    ·
                      rfl

theorem cell23_1621057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_1621057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621057 prefixEnd_1621057 := by exact prefixLift 1621057
  have htrace : WordTrace (prefixWord ++ tailWord_1621057) baseStart_1621057 baseEnd_1621057 := by
    simpa [prefixWord, tailWord_1621057, baseEnd_1621057] using wordTrace_append hprefix tailTrace_1621057
  have hstable : (prefixWord ++ tailWord_1621057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621057).length < 2 ^ (prefixWord ++ tailWord_1621057).sum := by decide
  have hdescent : baseEnd_1621057 < baseStart_1621057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621099 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 6]
def baseStart_1621099 : Nat := 118140960795 + 1621099 * 2 ^ 59
def prefixEnd_1621099 : Nat := 4983230072969 + 3 ^ 40 * 1621099 * 2
def baseEnd_1621099 : Nat := 832402975523058176407207

theorem tailTrace_1621099 : CollatzResearch.WordTrace tailWord_1621099 prefixEnd_1621099 832402975523058176407207 := by
  unfold tailWord_1621099
  simp only [CollatzResearch.WordTrace]
  refine ⟨59126337954042659512226351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39417558636028439674817567 59126337954042659512226351)
  ·
    refine ⟨88689506931063989268339527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59126337954042659512226351 88689506931063989268339527)
    ·
      refine ⟨133034260396595983902509291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88689506931063989268339527 133034260396595983902509291)
      ·
        refine ⟨199551390594893975853763937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133034260396595983902509291 199551390594893975853763937)
        ·
          refine ⟨149663542946170481890322953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199551390594893975853763937 149663542946170481890322953)
          ·
            refine ⟨112247657209627861417742215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149663542946170481890322953 112247657209627861417742215)
            ·
              refine ⟨168371485814441792126613323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112247657209627861417742215 168371485814441792126613323)
              ·
                refine ⟨252557228721662688189919985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168371485814441792126613323 252557228721662688189919985)
                ·
                  refine ⟨189417921541247016142439989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252557228721662688189919985 189417921541247016142439989)
                  ·
                    refine ⟨17757930144491907763353749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 189417921541247016142439989 17757930144491907763353749)
                    ·
                      refine ⟨832402975523058176407207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17757930144491907763353749 832402975523058176407207)
                      ·
                        rfl

theorem cell23_1621099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 6].length) (baseStart_1621099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621099 prefixEnd_1621099 := by exact prefixLift 1621099
  have htrace : WordTrace (prefixWord ++ tailWord_1621099) baseStart_1621099 baseEnd_1621099 := by
    simpa [prefixWord, tailWord_1621099, baseEnd_1621099] using wordTrace_append hprefix tailTrace_1621099
  have hstable : (prefixWord ++ tailWord_1621099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621099).length < 2 ^ (prefixWord ++ tailWord_1621099).sum := by decide
  have hdescent : baseEnd_1621099 < baseStart_1621099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621116 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_1621116 : Nat := 118140960795 + 1621116 * 2 ^ 59
def prefixEnd_1621116 : Nat := 4983230072969 + 3 ^ 40 * 1621116 * 2
def baseEnd_1621116 : Nat := 832411704694184609894629

theorem tailTrace_1621116 : CollatzResearch.WordTrace tailWord_1621116 prefixEnd_1621116 832411704694184609894629 := by
  unfold tailWord_1621116
  simp only [CollatzResearch.WordTrace]
  refine ⟨29563478997490535707797601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39417971996654047610396801 29563478997490535707797601)
  ·
    refine ⟨22172609248117901780848201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29563478997490535707797601 22172609248117901780848201)
    ·
      refine ⟨16629456936088426335636151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22172609248117901780848201 16629456936088426335636151)
      ·
        refine ⟨24944185404132639503454227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16629456936088426335636151 24944185404132639503454227)
        ·
          refine ⟨37416278106198959255181341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24944185404132639503454227 37416278106198959255181341)
          ·
            refine ⟨14031104289824609720693003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37416278106198959255181341 14031104289824609720693003)
            ·
              refine ⟨21046656434736914581039505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14031104289824609720693003 21046656434736914581039505)
              ·
                refine ⟨15784992326052685935779629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21046656434736914581039505 15784992326052685935779629)
                ·
                  refine ⟨5919372122269757225917361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15784992326052685935779629 5919372122269757225917361)
                  ·
                    refine ⟨4439529091702317919438021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5919372122269757225917361 4439529091702317919438021)
                    ·
                      refine ⟨832411704694184609894629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4439529091702317919438021 832411704694184609894629)
                      ·
                        rfl

theorem cell23_1621116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_1621116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621116 prefixEnd_1621116 := by exact prefixLift 1621116
  have htrace : WordTrace (prefixWord ++ tailWord_1621116) baseStart_1621116 baseEnd_1621116 := by
    simpa [prefixWord, tailWord_1621116, baseEnd_1621116] using wordTrace_append hprefix tailTrace_1621116
  have hstable : (prefixWord ++ tailWord_1621116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621116).length < 2 ^ (prefixWord ++ tailWord_1621116).sum := by decide
  have hdescent : baseEnd_1621116 < baseStart_1621116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621143 : List Nat := [1, 1, 3, 3, 3, 2, 3, 7]
def baseStart_1621143 : Nat := 118140960795 + 1621143 * 2 ^ 59
def prefixEnd_1621143 : Nat := 4983230072969 + 3 ^ 40 * 1621143 * 2
def baseEnd_1621143 : Nat := 30830576617476148305815

theorem tailTrace_1621143 : CollatzResearch.WordTrace tailWord_1621143 prefixEnd_1621143 30830576617476148305815 := by
  unfold tailWord_1621143
  simp only [CollatzResearch.WordTrace]
  refine ⟨59127942765883255026828083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39418628510588836684552055 59127942765883255026828083)
  ·
    refine ⟨88691914148824882540242125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59127942765883255026828083 88691914148824882540242125)
    ·
      refine ⟨33259467805809330952590797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88691914148824882540242125 33259467805809330952590797)
      ·
        refine ⟨12472300427178499107221549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33259467805809330952590797 12472300427178499107221549)
        ·
          refine ⟨4677112660191937165208081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12472300427178499107221549 4677112660191937165208081)
          ·
            refine ⟨3507834495143952873906061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4677112660191937165208081 3507834495143952873906061)
            ·
              refine ⟨1315437935678982327714773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3507834495143952873906061 1315437935678982327714773)
              ·
                refine ⟨30830576617476148305815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1315437935678982327714773 30830576617476148305815)
                ·
                  rfl

theorem cell23_1621143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 7].length) (baseStart_1621143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621143 prefixEnd_1621143 := by exact prefixLift 1621143
  have htrace : WordTrace (prefixWord ++ tailWord_1621143) baseStart_1621143 baseEnd_1621143 := by
    simpa [prefixWord, tailWord_1621143, baseEnd_1621143] using wordTrace_append hprefix tailTrace_1621143
  have hstable : (prefixWord ++ tailWord_1621143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621143).length < 2 ^ (prefixWord ++ tailWord_1621143).sum := by decide
  have hdescent : baseEnd_1621143 < baseStart_1621143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621150 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_1621150 : Nat := 118140960795 + 1621150 * 2 ^ 59
def prefixEnd_1621150 : Nat := 4983230072969 + 3 ^ 40 * 1621150 * 2
def baseEnd_1621150 : Nat := 832429163036437476869473

theorem tailTrace_1621150 : CollatzResearch.WordTrace tailWord_1621150 prefixEnd_1621150 832429163036437476869473 := by
  unfold tailWord_1621150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7391024759607236902791613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39418798717905263481555269 7391024759607236902791613)
  ·
    refine ⟨2771634284852713838546855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7391024759607236902791613 2771634284852713838546855)
    ·
      refine ⟨4157451427279070757820283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2771634284852713838546855 4157451427279070757820283)
      ·
        refine ⟨6236177140918606136730425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4157451427279070757820283 6236177140918606136730425)
        ·
          refine ⟨4677132855688954602547819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6236177140918606136730425 4677132855688954602547819)
          ·
            refine ⟨7015699283533431903821729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4677132855688954602547819 7015699283533431903821729)
            ·
              refine ⟨5261774462650073927866297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7015699283533431903821729 5261774462650073927866297)
              ·
                refine ⟨3946330846987555445899723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5261774462650073927866297 3946330846987555445899723)
                ·
                  refine ⟨5919496270481333168849585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3946330846987555445899723 5919496270481333168849585)
                  ·
                    refine ⟨4439622202860999876637189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5919496270481333168849585 4439622202860999876637189)
                    ·
                      refine ⟨832429163036437476869473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4439622202860999876637189 832429163036437476869473)
                      ·
                        rfl

theorem cell23_1621150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_1621150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621150 prefixEnd_1621150 := by exact prefixLift 1621150
  have htrace : WordTrace (prefixWord ++ tailWord_1621150) baseStart_1621150 baseEnd_1621150 := by
    simpa [prefixWord, tailWord_1621150, baseEnd_1621150] using wordTrace_append hprefix tailTrace_1621150
  have hstable : (prefixWord ++ tailWord_1621150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621150).length < 2 ^ (prefixWord ++ tailWord_1621150).sum := by decide
  have hdescent : baseEnd_1621150 < baseStart_1621150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621153 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 1, 3, 3]
def baseStart_1621153 : Nat := 118140960795 + 1621153 * 2 ^ 59
def prefixEnd_1621153 : Nat := 4983230072969 + 3 ^ 40 * 1621153 * 2
def baseEnd_1621153 : Nat := 832430703478400965131959

theorem tailTrace_1621153 : CollatzResearch.WordTrace tailWord_1621153 prefixEnd_1621153 832430703478400965131959 := by
  unfold tailWord_1621153
  simp only [CollatzResearch.WordTrace]
  refine ⟨59128307495847026734692113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39418871663898017823128075 59128307495847026734692113)
  ·
    refine ⟨44346230621885270051019085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59128307495847026734692113 44346230621885270051019085)
    ·
      refine ⟨16629836483206976269132157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44346230621885270051019085 16629836483206976269132157)
      ·
        refine ⟨6236188681202616100924559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16629836483206976269132157 6236188681202616100924559)
        ·
          refine ⟨9354283021803924151386839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6236188681202616100924559 9354283021803924151386839)
          ·
            refine ⟨14031424532705886227080259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9354283021803924151386839 14031424532705886227080259)
            ·
              refine ⟨21047136799058829340620389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14031424532705886227080259 21047136799058829340620389)
              ·
                refine ⟨3946338149823530501366323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21047136799058829340620389 3946338149823530501366323)
                ·
                  refine ⟨5919507224735295752049485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3946338149823530501366323 5919507224735295752049485)
                  ·
                    refine ⟨2219815209275735907018557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5919507224735295752049485 2219815209275735907018557)
                    ·
                      refine ⟨832430703478400965131959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2219815209275735907018557 832430703478400965131959)
                      ·
                        rfl

theorem cell23_1621153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_1621153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621153 prefixEnd_1621153 := by exact prefixLift 1621153
  have htrace : WordTrace (prefixWord ++ tailWord_1621153) baseStart_1621153 baseEnd_1621153 := by
    simpa [prefixWord, tailWord_1621153, baseEnd_1621153] using wordTrace_append hprefix tailTrace_1621153
  have hstable : (prefixWord ++ tailWord_1621153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621153).length < 2 ^ (prefixWord ++ tailWord_1621153).sum := by decide
  have hdescent : baseEnd_1621153 < baseStart_1621153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621154 : List Nat := [3, 3, 1, 3, 2, 2, 2, 1, 1, 1, 4]
def baseStart_1621154 : Nat := 118140960795 + 1621154 * 2 ^ 59
def prefixEnd_1621154 : Nat := 4983230072969 + 3 ^ 40 * 1621154 * 2
def baseEnd_1621154 : Nat := 832431216959055461219455

theorem tailTrace_1621154 : CollatzResearch.WordTrace tailWord_1621154 prefixEnd_1621154 832431216959055461219455 := by
  unfold tailWord_1621154
  simp only [CollatzResearch.WordTrace]
  refine ⟨14782085992210850976369629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39418895979228935936985677 14782085992210850976369629)
  ·
    refine ⟨5543282247079069116138611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14782085992210850976369629 5543282247079069116138611)
    ·
      refine ⟨8314923370618603674207917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5543282247079069116138611 8314923370618603674207917)
      ·
        refine ⟨3118096263981976377827969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8314923370618603674207917 3118096263981976377827969)
        ·
          refine ⟨2338572197986482283370977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3118096263981976377827969 2338572197986482283370977)
          ·
            refine ⟨1753929148489861712528233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2338572197986482283370977 1753929148489861712528233)
            ·
              refine ⟨1315446861367396284396175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1753929148489861712528233 1315446861367396284396175)
              ·
                refine ⟨1973170292051094426594263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315446861367396284396175 1973170292051094426594263)
                ·
                  refine ⟨2959755438076641639891395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1973170292051094426594263 2959755438076641639891395)
                  ·
                    refine ⟨4439633157114962459837093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2959755438076641639891395 4439633157114962459837093)
                    ·
                      refine ⟨832431216959055461219455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4439633157114962459837093 832431216959055461219455)
                      ·
                        rfl

theorem cell23_1621154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_1621154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621154 prefixEnd_1621154 := by exact prefixLift 1621154
  have htrace : WordTrace (prefixWord ++ tailWord_1621154) baseStart_1621154 baseEnd_1621154 := by
    simpa [prefixWord, tailWord_1621154, baseEnd_1621154] using wordTrace_append hprefix tailTrace_1621154
  have hstable : (prefixWord ++ tailWord_1621154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621154).length < 2 ^ (prefixWord ++ tailWord_1621154).sum := by decide
  have hdescent : baseEnd_1621154 < baseStart_1621154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621157 : List Nat := [1, 3, 1, 2, 1, 6, 2, 1, 1, 2, 3]
def baseStart_1621157 : Nat := 118140960795 + 1621157 * 2 ^ 59
def prefixEnd_1621157 : Nat := 4983230072969 + 3 ^ 40 * 1621157 * 2
def baseEnd_1621157 : Nat := 832432757401018949481941

theorem tailTrace_1621157 : CollatzResearch.WordTrace tailWord_1621157 prefixEnd_1621157 832432757401018949481941 := by
  unfold tailWord_1621157
  simp only [CollatzResearch.WordTrace]
  refine ⟨59128453387832535417837725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39418968925221690278558483 59128453387832535417837725)
  ·
    refine ⟨22173170020437200781689147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59128453387832535417837725 22173170020437200781689147)
    ·
      refine ⟨33259755030655801172533721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22173170020437200781689147 33259755030655801172533721)
      ·
        refine ⟨24944816272991850879400291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33259755030655801172533721 24944816272991850879400291)
        ·
          refine ⟨37417224409487776319100437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24944816272991850879400291 37417224409487776319100437)
          ·
            refine ⟨1753932394194739514957833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37417224409487776319100437 1753932394194739514957833)
            ·
              refine ⟨1315449295646054636218375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1753932394194739514957833 1315449295646054636218375)
              ·
                refine ⟨1973173943469081954327563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315449295646054636218375 1973173943469081954327563)
                ·
                  refine ⟨2959760915203622931491345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1973173943469081954327563 2959760915203622931491345)
                  ·
                    refine ⟨2219820686402717198618509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2959760915203622931491345 2219820686402717198618509)
                    ·
                      refine ⟨832432757401018949481941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2219820686402717198618509 832432757401018949481941)
                      ·
                        rfl

theorem cell23_1621157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_1621157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621157 prefixEnd_1621157 := by exact prefixLift 1621157
  have htrace : WordTrace (prefixWord ++ tailWord_1621157) baseStart_1621157 baseEnd_1621157 := by
    simpa [prefixWord, tailWord_1621157, baseEnd_1621157] using wordTrace_append hprefix tailTrace_1621157
  have hstable : (prefixWord ++ tailWord_1621157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621157).length < 2 ^ (prefixWord ++ tailWord_1621157).sum := by decide
  have hdescent : baseEnd_1621157 < baseStart_1621157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621170 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3]
def baseStart_1621170 : Nat := 118140960795 + 1621170 * 2 ^ 59
def prefixEnd_1621170 : Nat := 4983230072969 + 3 ^ 40 * 1621170 * 2
def baseEnd_1621170 : Nat := 832439432649527398619381

theorem tailTrace_1621170 : CollatzResearch.WordTrace tailWord_1621170 prefixEnd_1621170 832439432649527398619381 := by
  unfold tailWord_1621170
  simp only [CollatzResearch.WordTrace]
  refine ⟨14782231884196359659515241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39419285024523625758707309 14782231884196359659515241)
  ·
    refine ⟨11086673913147269744636431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14782231884196359659515241 11086673913147269744636431)
    ·
      refine ⟨16630010869720904616954647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11086673913147269744636431 16630010869720904616954647)
      ·
        refine ⟨24945016304581356925431971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16630010869720904616954647 24945016304581356925431971)
        ·
          refine ⟨37417524456872035388147957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24945016304581356925431971 37417524456872035388147957)
          ·
            refine ⟨3507892917831753317638871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37417524456872035388147957 3507892917831753317638871)
            ·
              refine ⟨5261839376747629976458307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3507892917831753317638871 5261839376747629976458307)
              ·
                refine ⟨7892759065121444964687461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5261839376747629976458307 7892759065121444964687461)
                ·
                  refine ⟨1479892324710270930878899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7892759065121444964687461 1479892324710270930878899)
                  ·
                    refine ⟨2219838487065406396318349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1479892324710270930878899 2219838487065406396318349)
                    ·
                      refine ⟨832439432649527398619381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2219838487065406396318349 832439432649527398619381)
                      ·
                        rfl

theorem cell23_1621170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_1621170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621170 prefixEnd_1621170 := by exact prefixLift 1621170
  have htrace : WordTrace (prefixWord ++ tailWord_1621170) baseStart_1621170 baseEnd_1621170 := by
    simpa [prefixWord, tailWord_1621170, baseEnd_1621170] using wordTrace_append hprefix tailTrace_1621170
  have hstable : (prefixWord ++ tailWord_1621170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621170).length < 2 ^ (prefixWord ++ tailWord_1621170).sum := by decide
  have hdescent : baseEnd_1621170 < baseStart_1621170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621176 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 4]
def baseStart_1621176 : Nat := 118140960795 + 1621176 * 2 ^ 59
def prefixEnd_1621176 : Nat := 4983230072969 + 3 ^ 40 * 1621176 * 2
def baseEnd_1621176 : Nat := 832442513533454375144353

theorem tailTrace_1621176 : CollatzResearch.WordTrace tailWord_1621176 prefixEnd_1621176 832442513533454375144353 := by
  unfold tailWord_1621176
  simp only [CollatzResearch.WordTrace]
  refine ⟨29564573187381850831389691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39419430916509134441852921 29564573187381850831389691)
  ·
    refine ⟨44346859781072776247084537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29564573187381850831389691 44346859781072776247084537)
    ·
      refine ⟨33260144835804582185313403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44346859781072776247084537 33260144835804582185313403)
      ·
        refine ⟨49890217253706873277970105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33260144835804582185313403 49890217253706873277970105)
        ·
          refine ⟨37417662940280154958477579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49890217253706873277970105 37417662940280154958477579)
          ·
            refine ⟨56126494410420232437716369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37417662940280154958477579 56126494410420232437716369)
            ·
              refine ⟨42094870807815174328287277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56126494410420232437716369 42094870807815174328287277)
              ·
                refine ⟨15785576552930690373107729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42094870807815174328287277 15785576552930690373107729)
                ·
                  refine ⟨11839182414698017779830797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15785576552930690373107729 11839182414698017779830797)
                  ·
                    refine ⟨4439693405511756667436549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11839182414698017779830797 4439693405511756667436549)
                    ·
                      refine ⟨832442513533454375144353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4439693405511756667436549 832442513533454375144353)
                      ·
                        rfl

theorem cell23_1621176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_1621176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621176 prefixEnd_1621176 := by exact prefixLift 1621176
  have htrace : WordTrace (prefixWord ++ tailWord_1621176) baseStart_1621176 baseEnd_1621176 := by
    simpa [prefixWord, tailWord_1621176, baseEnd_1621176] using wordTrace_append hprefix tailTrace_1621176
  have hstable : (prefixWord ++ tailWord_1621176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621176).length < 2 ^ (prefixWord ++ tailWord_1621176).sum := by decide
  have hdescent : baseEnd_1621176 < baseStart_1621176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621244 : List Nat := [2, 2, 2, 1, 5, 1, 1, 3, 2, 2, 2]
def baseStart_1621244 : Nat := 118140960795 + 1621244 * 2 ^ 59
def prefixEnd_1621244 : Nat := 4983230072969 + 3 ^ 40 * 1621244 * 2
def baseEnd_1621244 : Nat := 832477430217960109094041

theorem tailTrace_1621244 : CollatzResearch.WordTrace tailWord_1621244 prefixEnd_1621244 832477430217960109094041 := by
  unfold tailWord_1621244
  simp only [CollatzResearch.WordTrace]
  refine ⟨29565813269258674638127393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39421084359011566184169857 29565813269258674638127393)
  ·
    refine ⟨22174359951944005978595545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29565813269258674638127393 22174359951944005978595545)
    ·
      refine ⟨16630769963958004483946659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22174359951944005978595545 16630769963958004483946659)
      ·
        refine ⟨24946154945937006725919989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16630769963958004483946659 24946154945937006725919989)
        ·
          refine ⟨2338702026181594380554999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24946154945937006725919989 2338702026181594380554999)
          ·
            refine ⟨3508053039272391570832499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338702026181594380554999 3508053039272391570832499)
            ·
              refine ⟨5262079558908587356248749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3508053039272391570832499 5262079558908587356248749)
              ·
                refine ⟨1973279834590720258593281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5262079558908587356248749 1973279834590720258593281)
                ·
                  refine ⟨1479959875943040193944961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1973279834590720258593281 1479959875943040193944961)
                  ·
                    refine ⟨1109969906957280145458721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1479959875943040193944961 1109969906957280145458721)
                    ·
                      refine ⟨832477430217960109094041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1109969906957280145458721 832477430217960109094041)
                      ·
                        rfl

theorem cell23_1621244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_1621244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621244 prefixEnd_1621244 := by exact prefixLift 1621244
  have htrace : WordTrace (prefixWord ++ tailWord_1621244) baseStart_1621244 baseEnd_1621244 := by
    simpa [prefixWord, tailWord_1621244, baseEnd_1621244] using wordTrace_append hprefix tailTrace_1621244
  have hstable : (prefixWord ++ tailWord_1621244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621244).length < 2 ^ (prefixWord ++ tailWord_1621244).sum := by decide
  have hdescent : baseEnd_1621244 < baseStart_1621244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621278 : List Nat := [4, 3, 2, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_1621278 : Nat := 118140960795 + 1621278 * 2 ^ 59
def prefixEnd_1621278 : Nat := 4983230072969 + 3 ^ 40 * 1621278 * 2
def baseEnd_1621278 : Nat := 832494888560212976068885

theorem tailTrace_1621278 : CollatzResearch.WordTrace tailWord_1621278 prefixEnd_1621278 832494888560212976068885 := by
  unfold tailWord_1621278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7391608327549271635374061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39421911080262782055328325 7391608327549271635374061)
  ·
    refine ⟨2771853122830976863265273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7391608327549271635374061 2771853122830976863265273)
    ·
      refine ⟨2078889842123232647448955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2771853122830976863265273 2078889842123232647448955)
      ·
        refine ⟨3118334763184848971173433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2078889842123232647448955 3118334763184848971173433)
        ·
          refine ⟨2338751072388636728380075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3118334763184848971173433 2338751072388636728380075)
          ·
            refine ⟨3508126608582955092570113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338751072388636728380075 3508126608582955092570113)
            ·
              refine ⟨2631094956437216319427585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3508126608582955092570113 2631094956437216319427585)
              ·
                refine ⟨1973321217327912239570689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2631094956437216319427585 1973321217327912239570689)
                ·
                  refine ⟨1479990912995934179678017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1973321217327912239570689 1479990912995934179678017)
                  ·
                    refine ⟨1109993184746950634758513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1479990912995934179678017 1109993184746950634758513)
                    ·
                      refine ⟨832494888560212976068885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1109993184746950634758513 832494888560212976068885)
                      ·
                        rfl

theorem cell23_1621278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_1621278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621278 prefixEnd_1621278 := by exact prefixLift 1621278
  have htrace : WordTrace (prefixWord ++ tailWord_1621278) baseStart_1621278 baseEnd_1621278 := by
    simpa [prefixWord, tailWord_1621278, baseEnd_1621278] using wordTrace_append hprefix tailTrace_1621278
  have hstable : (prefixWord ++ tailWord_1621278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621278).length < 2 ^ (prefixWord ++ tailWord_1621278).sum := by decide
  have hdescent : baseEnd_1621278 < baseStart_1621278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621290 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1621290 : Nat := 118140960795 + 1621290 * 2 ^ 59
def prefixEnd_1621290 : Nat := 4983230072969 + 3 ^ 40 * 1621290 * 2
def baseEnd_1621290 : Nat := 832501050328066929118829

theorem tailTrace_1621290 : CollatzResearch.WordTrace tailWord_1621290 prefixEnd_1621290 832501050328066929118829 := by
  unfold tailWord_1621290
  simp only [CollatzResearch.WordTrace]
  refine ⟨14783326074087674783107331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39422202864233799421619549 14783326074087674783107331)
  ·
    refine ⟨22174989111131512174660997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14783326074087674783107331 22174989111131512174660997)
    ·
      refine ⟨4157810458337158532748937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22174989111131512174660997 4157810458337158532748937)
      ·
        refine ⟨3118357843752868899561703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4157810458337158532748937 3118357843752868899561703)
        ·
          refine ⟨4677536765629303349342555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3118357843752868899561703 4677536765629303349342555)
          ·
            refine ⟨7016305148443955024013833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4677536765629303349342555 7016305148443955024013833)
            ·
              refine ⟨5262228861332966268010375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7016305148443955024013833 5262228861332966268010375)
              ·
                refine ⟨7893343291999449402015563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5262228861332966268010375 7893343291999449402015563)
                ·
                  refine ⟨11840014937999174103023345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7893343291999449402015563 11840014937999174103023345)
                  ·
                    refine ⟨8880011203499380577267509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11840014937999174103023345 8880011203499380577267509)
                    ·
                      refine ⟨832501050328066929118829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8880011203499380577267509 832501050328066929118829)
                      ·
                        rfl

theorem cell23_1621290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1621290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621290 prefixEnd_1621290 := by exact prefixLift 1621290
  have htrace : WordTrace (prefixWord ++ tailWord_1621290) baseStart_1621290 baseEnd_1621290 := by
    simpa [prefixWord, tailWord_1621290, baseEnd_1621290] using wordTrace_append hprefix tailTrace_1621290
  have hstable : (prefixWord ++ tailWord_1621290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621290).length < 2 ^ (prefixWord ++ tailWord_1621290).sum := by decide
  have hdescent : baseEnd_1621290 < baseStart_1621290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621300 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1621300 : Nat := 118140960795 + 1621300 * 2 ^ 59
def prefixEnd_1621300 : Nat := 4983230072969 + 3 ^ 40 * 1621300 * 2
def baseEnd_1621300 : Nat := 832506185134611889993783

theorem tailTrace_1621300 : CollatzResearch.WordTrace tailWord_1621300 prefixEnd_1621300 832506185134611889993783 := by
  unfold tailWord_1621300
  simp only [CollatzResearch.WordTrace]
  refine ⟨29566834513157235420146677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39422446017542980560195569 29566834513157235420146677)
  ·
    refine ⟨2771890735608490820638751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29566834513157235420146677 2771890735608490820638751)
    ·
      refine ⟨4157836103412736230958127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2771890735608490820638751 4157836103412736230958127)
      ·
        refine ⟨6236754155119104346437191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4157836103412736230958127 6236754155119104346437191)
        ·
          refine ⟨9355131232678656519655787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6236754155119104346437191 9355131232678656519655787)
          ·
            refine ⟨14032696849017984779483681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9355131232678656519655787 14032696849017984779483681)
            ·
              refine ⟨10524522636763488584612761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14032696849017984779483681 10524522636763488584612761)
              ·
                refine ⟨7893391977572616438459571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10524522636763488584612761 7893391977572616438459571)
                ·
                  refine ⟨11840087966358924657689357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7893391977572616438459571 11840087966358924657689357)
                  ·
                    refine ⟨4440032987384596746633509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11840087966358924657689357 4440032987384596746633509)
                    ·
                      refine ⟨832506185134611889993783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4440032987384596746633509 832506185134611889993783)
                      ·
                        rfl

theorem cell23_1621300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1621300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621300 prefixEnd_1621300 := by exact prefixLift 1621300
  have htrace : WordTrace (prefixWord ++ tailWord_1621300) baseStart_1621300 baseEnd_1621300 := by
    simpa [prefixWord, tailWord_1621300, baseEnd_1621300] using wordTrace_append hprefix tailTrace_1621300
  have hstable : (prefixWord ++ tailWord_1621300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621300).length < 2 ^ (prefixWord ++ tailWord_1621300).sum := by decide
  have hdescent : baseEnd_1621300 < baseStart_1621300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
