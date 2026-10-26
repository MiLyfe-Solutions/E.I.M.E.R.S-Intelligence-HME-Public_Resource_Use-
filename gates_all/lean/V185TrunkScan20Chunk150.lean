import V185TrunkScan20Chunk149

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_912227 : List Nat := [1, 1, 1, 5, 3, 2, 7]
def baseStart_912227 : Nat := 118140960795 + 912227 * 2 ^ 59
def prefixEnd_912227 : Nat := 4983230072969 + 3 ^ 40 * 912227 * 2
def baseEnd_912227 : Nat := 46262806618183470752321

theorem tailTrace_912227 : CollatzResearch.WordTrace tailWord_912227 prefixEnd_912227 46262806618183470752321 := by
  unfold tailWord_912227
  simp only [CollatzResearch.WordTrace]
  refine ⟨33271652066164849813158935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22181101377443233208772623 33271652066164849813158935)
  ·
    refine ⟨49907478099247274719738403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33271652066164849813158935 49907478099247274719738403)
    ·
      refine ⟨74861217148870912079607605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49907478099247274719738403 74861217148870912079607605)
      ·
        refine ⟨7018239107706648007463213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74861217148870912079607605 7018239107706648007463213)
        ·
          refine ⟨2631839665389993002798705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7018239107706648007463213 2631839665389993002798705)
          ·
            refine ⟨1973879749042494752099029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2631839665389993002798705 1973879749042494752099029)
            ·
              refine ⟨46262806618183470752321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1973879749042494752099029 46262806618183470752321)
              ·
                rfl

theorem cell20_912227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 7].length) (baseStart_912227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912227 prefixEnd_912227 := by exact prefixLift 912227
  have htrace : WordTrace (prefixWord ++ tailWord_912227) baseStart_912227 baseEnd_912227 := by
    simpa [prefixWord, tailWord_912227, baseEnd_912227] using wordTrace_append hprefix tailTrace_912227
  have hstable : (prefixWord ++ tailWord_912227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912227).length < 2 ^ (prefixWord ++ tailWord_912227).sum := by decide
  have hdescent : baseEnd_912227 < baseStart_912227 := by decide
  rcases family_descends (prefixWord ++ tailWord_912227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912265 : List Nat := [1, 2, 1, 1, 5, 3, 1, 6]
def baseStart_912265 : Nat := 118140960795 + 912265 * 2 ^ 59
def prefixEnd_912265 : Nat := 4983230072969 + 3 ^ 40 * 912265 * 2
def baseEnd_912265 : Nat := 138794201266363997834689

theorem tailTrace_912265 : CollatzResearch.WordTrace tailWord_912265 prefixEnd_912265 138794201266363997834689 := by
  unfold tailWord_912265
  simp only [CollatzResearch.WordTrace]
  refine ⟨33273038040027182303042249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22182025360018121535361499 33273038040027182303042249)
  ·
    refine ⟨24954778530020386727281687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33273038040027182303042249 24954778530020386727281687)
    ·
      refine ⟨37432167795030580090922531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24954778530020386727281687 37432167795030580090922531)
      ·
        refine ⟨56148251692545870136383797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37432167795030580090922531 56148251692545870136383797)
        ·
          refine ⟨5263898596176175325285981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56148251692545870136383797 5263898596176175325285981)
          ·
            refine ⟨1973961973566065746982243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5263898596176175325285981 1973961973566065746982243)
            ·
              refine ⟨2960942960349098620473365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973961973566065746982243 2960942960349098620473365)
              ·
                refine ⟨138794201266363997834689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2960942960349098620473365 138794201266363997834689)
                ·
                  rfl

theorem cell20_912265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 6].length) (baseStart_912265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912265 prefixEnd_912265 := by exact prefixLift 912265
  have htrace : WordTrace (prefixWord ++ tailWord_912265) baseStart_912265 baseEnd_912265 := by
    simpa [prefixWord, tailWord_912265, baseEnd_912265] using wordTrace_append hprefix tailTrace_912265
  have hstable : (prefixWord ++ tailWord_912265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912265).length < 2 ^ (prefixWord ++ tailWord_912265).sum := by decide
  have hdescent : baseEnd_912265 < baseStart_912265 := by decide
  rcases family_descends (prefixWord ++ tailWord_912265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912278 : List Nat := [5, 3, 1, 1, 1, 3, 6]
def baseStart_912278 : Nat := 118140960795 + 912278 * 2 ^ 59
def prefixEnd_912278 : Nat := 4983230072969 + 3 ^ 40 * 912278 * 2
def baseEnd_912278 : Nat := 46265393039257969563409

theorem tailTrace_912278 : CollatzResearch.WordTrace tailWord_912278 prefixEnd_912278 46265393039257969563409 := by
  unfold tailWord_912278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2079594511811255345204093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22182341459320057015510325 2079594511811255345204093)
  ·
    refine ⟨779847941929220754451535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2079594511811255345204093 779847941929220754451535)
    ·
      refine ⟨1169771912893831131677303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 779847941929220754451535 1169771912893831131677303)
      ·
        refine ⟨1754657869340746697515955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1169771912893831131677303 1754657869340746697515955)
        ·
          refine ⟨2631986804011120046273933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754657869340746697515955 2631986804011120046273933)
          ·
            refine ⟨986995051504170017352725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2631986804011120046273933 986995051504170017352725)
            ·
              refine ⟨46265393039257969563409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 986995051504170017352725 46265393039257969563409)
              ·
                rfl

theorem cell20_912278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 6].length) (baseStart_912278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912278 prefixEnd_912278 := by exact prefixLift 912278
  have htrace : WordTrace (prefixWord ++ tailWord_912278) baseStart_912278 baseEnd_912278 := by
    simpa [prefixWord, tailWord_912278, baseEnd_912278] using wordTrace_append hprefix tailTrace_912278
  have hstable : (prefixWord ++ tailWord_912278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912278).length < 2 ^ (prefixWord ++ tailWord_912278).sum := by decide
  have hdescent : baseEnd_912278 < baseStart_912278 := by decide
  rcases family_descends (prefixWord ++ tailWord_912278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912282 : List Nat := [3, 1, 1, 4, 3, 2, 6]
def baseStart_912282 : Nat := 118140960795 + 912282 * 2 ^ 59
def prefixEnd_912282 : Nat := 4983230072969 + 3 ^ 40 * 912282 * 2
def baseEnd_912282 : Nat := 46265595895812832215259

theorem tailTrace_912282 : CollatzResearch.WordTrace tailWord_912282 prefixEnd_912282 46265595895812832215259 := by
  unfold tailWord_912282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8318414520241398551602775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22182438720643729470940733 8318414520241398551602775)
  ·
    refine ⟨12477621780362097827404163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8318414520241398551602775 12477621780362097827404163)
    ·
      refine ⟨18716432670543146741106245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12477621780362097827404163 18716432670543146741106245)
      ·
        refine ⟨3509331125726840013957421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18716432670543146741106245 3509331125726840013957421)
        ·
          refine ⟨1315999172147565005234033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3509331125726840013957421 1315999172147565005234033)
          ·
            refine ⟨986999379110673753925525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1315999172147565005234033 986999379110673753925525)
            ·
              refine ⟨46265595895812832215259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 986999379110673753925525 46265595895812832215259)
              ·
                rfl

theorem cell20_912282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 6].length) (baseStart_912282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912282 prefixEnd_912282 := by exact prefixLift 912282
  have htrace : WordTrace (prefixWord ++ tailWord_912282) baseStart_912282 baseEnd_912282 := by
    simpa [prefixWord, tailWord_912282, baseEnd_912282] using wordTrace_append hprefix tailTrace_912282
  have hstable : (prefixWord ++ tailWord_912282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912282).length < 2 ^ (prefixWord ++ tailWord_912282).sum := by decide
  have hdescent : baseEnd_912282 < baseStart_912282 := by decide
  rcases family_descends (prefixWord ++ tailWord_912282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912289 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 5]
def baseStart_912289 : Nat := 118140960795 + 912289 * 2 ^ 59
def prefixEnd_912289 : Nat := 4983230072969 + 3 ^ 40 * 912289 * 2
def baseEnd_912289 : Nat := 416393558053054576703969

theorem tailTrace_912289 : CollatzResearch.WordTrace tailWord_912289 prefixEnd_912289 416393558053054576703969 := by
  unfold tailWord_912289
  simp only [CollatzResearch.WordTrace]
  refine ⟨33273913391940234401915921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22182608927960156267943947 33273913391940234401915921)
  ·
    refine ⟨24955435043955175801436941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33273913391940234401915921 24955435043955175801436941)
    ·
      refine ⟨9358288141483190925538853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24955435043955175801436941 9358288141483190925538853)
      ·
        refine ⟨1754679026528098298538535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9358288141483190925538853 1754679026528098298538535)
        ·
          refine ⟨2632018539792147447807803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754679026528098298538535 2632018539792147447807803)
          ·
            refine ⟨3948027809688221171711705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632018539792147447807803 3948027809688221171711705)
            ·
              refine ⟨2961020857266165878783779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3948027809688221171711705 2961020857266165878783779)
              ·
                refine ⟨4441531285899248818175669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2961020857266165878783779 4441531285899248818175669)
                ·
                  refine ⟨416393558053054576703969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4441531285899248818175669 416393558053054576703969)
                  ·
                    rfl

theorem cell20_912289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_912289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912289 prefixEnd_912289 := by exact prefixLift 912289
  have htrace : WordTrace (prefixWord ++ tailWord_912289) baseStart_912289 baseEnd_912289 := by
    simpa [prefixWord, tailWord_912289, baseEnd_912289] using wordTrace_append hprefix tailTrace_912289
  have hstable : (prefixWord ++ tailWord_912289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912289).length < 2 ^ (prefixWord ++ tailWord_912289).sum := by decide
  have hdescent : baseEnd_912289 < baseStart_912289 := by decide
  rcases family_descends (prefixWord ++ tailWord_912289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912292 : List Nat := [2, 3, 1, 2, 1, 2, 5, 2, 2]
def baseStart_912292 : Nat := 118140960795 + 912292 * 2 ^ 59
def prefixEnd_912292 : Nat := 4983230072969 + 3 ^ 40 * 912292 * 2
def baseEnd_912292 : Nat := 416394927334799899603957

theorem tailTrace_912292 : CollatzResearch.WordTrace tailWord_912292 prefixEnd_912292 416394927334799899603957 := by
  unfold tailWord_912292
  simp only [CollatzResearch.WordTrace]
  refine ⟨16637011405464682957137565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22182681873952910609516753 16637011405464682957137565)
  ·
    refine ⟨6238879277049256108926587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16637011405464682957137565 6238879277049256108926587)
    ·
      refine ⟨9358318915573884163389881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6238879277049256108926587 9358318915573884163389881)
      ·
        refine ⟨7018739186680413122542411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9358318915573884163389881 7018739186680413122542411)
        ·
          refine ⟨10528108780020619683813617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7018739186680413122542411 10528108780020619683813617)
          ·
            refine ⟨7896081585015464762860213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10528108780020619683813617 7896081585015464762860213)
            ·
              refine ⟨740257648595199821518145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7896081585015464762860213 740257648595199821518145)
              ·
                refine ⟨555193236446399866138609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740257648595199821518145 555193236446399866138609)
                ·
                  refine ⟨416394927334799899603957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555193236446399866138609 416394927334799899603957)
                  ·
                    rfl

theorem cell20_912292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_912292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912292 prefixEnd_912292 := by exact prefixLift 912292
  have htrace : WordTrace (prefixWord ++ tailWord_912292) baseStart_912292 baseEnd_912292 := by
    simpa [prefixWord, tailWord_912292, baseEnd_912292] using wordTrace_append hprefix tailTrace_912292
  have hstable : (prefixWord ++ tailWord_912292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912292).length < 2 ^ (prefixWord ++ tailWord_912292).sum := by decide
  have hdescent : baseEnd_912292 < baseStart_912292 := by decide
  rcases family_descends (prefixWord ++ tailWord_912292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912341 : List Nat := [1, 3, 2, 3, 3, 8]
def baseStart_912341 : Nat := 118140960795 + 912341 * 2 ^ 59
def prefixEnd_912341 : Nat := 4983230072969 + 3 ^ 40 * 912341 * 2
def baseEnd_912341 : Nat := 15422862676665685443349

theorem tailTrace_912341 : CollatzResearch.WordTrace tailWord_912341 prefixEnd_912341 15422862676665685443349 := by
  unfold tailWord_912341
  simp only [CollatzResearch.WordTrace]
  refine ⟨33275809987751847282808877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22183873325167898188539251 33275809987751847282808877)
  ·
    refine ⟨12478428745406942731053329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33275809987751847282808877 12478428745406942731053329)
    ·
      refine ⟨9358821559055207048289997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12478428745406942731053329 9358821559055207048289997)
      ·
        refine ⟨3509558084645702643108749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9358821559055207048289997 3509558084645702643108749)
        ·
          refine ⟨1316084281742138491165781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3509558084645702643108749 1316084281742138491165781)
          ·
            refine ⟨15422862676665685443349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1316084281742138491165781 15422862676665685443349)
            ·
              rfl

theorem cell20_912341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 8].length) (baseStart_912341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912341 prefixEnd_912341 := by exact prefixLift 912341
  have htrace : WordTrace (prefixWord ++ tailWord_912341) baseStart_912341 baseEnd_912341 := by
    simpa [prefixWord, tailWord_912341, baseEnd_912341] using wordTrace_append hprefix tailTrace_912341
  have hstable : (prefixWord ++ tailWord_912341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912341).length < 2 ^ (prefixWord ++ tailWord_912341).sum := by decide
  have hdescent : baseEnd_912341 < baseStart_912341 := by decide
  rcases family_descends (prefixWord ++ tailWord_912341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912389 : List Nat := [1, 3, 1, 1, 2, 3, 4, 3, 2]
def baseStart_912389 : Nat := 118140960795 + 912389 * 2 ^ 59
def prefixEnd_912389 : Nat := 4983230072969 + 3 ^ 40 * 912389 * 2
def baseEnd_912389 : Nat := 416439200777898673370227

theorem tailTrace_912389 : CollatzResearch.WordTrace tailWord_912389 prefixEnd_912389 416439200777898673370227 := by
  unfold tailWord_912389
  simp only [CollatzResearch.WordTrace]
  refine ⟨33277560691577951480556221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22185040461051967653704147 33277560691577951480556221)
  ·
    refine ⟨12479085259341731805208583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33277560691577951480556221 12479085259341731805208583)
    ·
      refine ⟨18718627889012597707812875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12479085259341731805208583 18718627889012597707812875)
      ·
        refine ⟨28077941833518896561719313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18718627889012597707812875 28077941833518896561719313)
        ·
          refine ⟨21058456375139172421289485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28077941833518896561719313 21058456375139172421289485)
          ·
            refine ⟨7896921140677189657983557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21058456375139172421289485 7896921140677189657983557)
            ·
              refine ⟨1480672713876973060871917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7896921140677189657983557 1480672713876973060871917)
              ·
                refine ⟨555252267703864897826969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1480672713876973060871917 555252267703864897826969)
                ·
                  refine ⟨416439200777898673370227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555252267703864897826969 416439200777898673370227)
                  ·
                    rfl

theorem cell20_912389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_912389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912389 prefixEnd_912389 := by exact prefixLift 912389
  have htrace : WordTrace (prefixWord ++ tailWord_912389) baseStart_912389 baseEnd_912389 := by
    simpa [prefixWord, tailWord_912389, baseEnd_912389] using wordTrace_append hprefix tailTrace_912389
  have hstable : (prefixWord ++ tailWord_912389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912389).length < 2 ^ (prefixWord ++ tailWord_912389).sum := by decide
  have hdescent : baseEnd_912389 < baseStart_912389 := by decide
  rcases family_descends (prefixWord ++ tailWord_912389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912410 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_912410 : Nat := 118140960795 + 912410 * 2 ^ 59
def prefixEnd_912410 : Nat := 4983230072969 + 3 ^ 40 * 912410 * 2
def baseEnd_912410 : Nat := 416448785750115933670141

theorem tailTrace_912410 : CollatzResearch.WordTrace tailWord_912410 prefixEnd_912410 416448785750115933670141 := by
  unfold tailWord_912410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8319581656125468016767671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22185551083001248044713789 8319581656125468016767671)
  ·
    refine ⟨12479372484188202025151507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8319581656125468016767671 12479372484188202025151507)
    ·
      refine ⟨18719058726282303037727261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12479372484188202025151507 18719058726282303037727261)
      ·
        refine ⟨7019647022355863639147723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18719058726282303037727261 7019647022355863639147723)
        ·
          refine ⟨10529470533533795458721585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7019647022355863639147723 10529470533533795458721585)
          ·
            refine ⟨7897102900150346594041189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10529470533533795458721585 7897102900150346594041189)
            ·
              refine ⟨1480706793778189986382723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7897102900150346594041189 1480706793778189986382723)
              ·
                refine ⟨2221060190667284979574085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1480706793778189986382723 2221060190667284979574085)
                ·
                  refine ⟨416448785750115933670141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2221060190667284979574085 416448785750115933670141)
                  ·
                    rfl

theorem cell20_912410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_912410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912410 prefixEnd_912410 := by exact prefixLift 912410
  have htrace : WordTrace (prefixWord ++ tailWord_912410) baseStart_912410 baseEnd_912410 := by
    simpa [prefixWord, tailWord_912410, baseEnd_912410] using wordTrace_append hprefix tailTrace_912410
  have hstable : (prefixWord ++ tailWord_912410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912410).length < 2 ^ (prefixWord ++ tailWord_912410).sum := by decide
  have hdescent : baseEnd_912410 < baseStart_912410 := by decide
  rcases family_descends (prefixWord ++ tailWord_912410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912444 : List Nat := [2, 2, 2, 2, 2, 4, 1, 3, 2]
def baseStart_912444 : Nat := 118140960795 + 912444 * 2 ^ 59
def prefixEnd_912444 : Nat := 4983230072969 + 3 ^ 40 * 912444 * 2
def baseEnd_912444 : Nat := 416464304276562926536669

theorem tailTrace_912444 : CollatzResearch.WordTrace tailWord_912444 prefixEnd_912444 416464304276562926536669 := by
  unfold tailWord_912444
  simp only [CollatzResearch.WordTrace]
  refine ⟨16639783353189347936904193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22186377804252463915872257 16639783353189347936904193)
  ·
    refine ⟨12479837514892010952678145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16639783353189347936904193 12479837514892010952678145)
    ·
      refine ⟨9359878136169008214508609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12479837514892010952678145 9359878136169008214508609)
      ·
        refine ⟨7019908602126756160881457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9359878136169008214508609 7019908602126756160881457)
        ·
          refine ⟨5264931451595067120661093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7019908602126756160881457 5264931451595067120661093)
          ·
            refine ⟨987174647174075085123955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5264931451595067120661093 987174647174075085123955)
            ·
              refine ⟨1480761970761112627685933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987174647174075085123955 1480761970761112627685933)
              ·
                refine ⟨555285739035417235382225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1480761970761112627685933 555285739035417235382225)
                ·
                  refine ⟨416464304276562926536669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555285739035417235382225 416464304276562926536669)
                  ·
                    rfl

theorem cell20_912444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_912444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912444 prefixEnd_912444 := by exact prefixLift 912444
  have htrace : WordTrace (prefixWord ++ tailWord_912444) baseStart_912444 baseEnd_912444 := by
    simpa [prefixWord, tailWord_912444, baseEnd_912444] using wordTrace_append hprefix tailTrace_912444
  have hstable : (prefixWord ++ tailWord_912444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912444).length < 2 ^ (prefixWord ++ tailWord_912444).sum := by decide
  have hdescent : baseEnd_912444 < baseStart_912444 := by decide
  rcases family_descends (prefixWord ++ tailWord_912444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912455 : List Nat := [1, 1, 4, 1, 3, 4, 6]
def baseStart_912455 : Nat := 118140960795 + 912455 * 2 ^ 59
def prefixEnd_912455 : Nat := 4983230072969 + 3 ^ 40 * 912455 * 2
def baseEnd_912455 : Nat := 46274369441810641907773

theorem tailTrace_912455 : CollatzResearch.WordTrace tailWord_912455 prefixEnd_912455 46274369441810641907773 := by
  unfold tailWord_912455
  simp only [CollatzResearch.WordTrace]
  refine ⟨33279967909338844752458819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22186645272892563168305879 33279967909338844752458819)
  ·
    refine ⟨49919951864008267128688229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33279967909338844752458819 49919951864008267128688229)
    ·
      refine ⟨9359990974501550086629043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49919951864008267128688229 9359990974501550086629043)
      ·
        refine ⟨14039986461752325129943565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9359990974501550086629043 14039986461752325129943565)
        ·
          refine ⟨5264994923157121923728837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14039986461752325129943565 5264994923157121923728837)
          ·
            refine ⟨987186548091960360699157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5264994923157121923728837 987186548091960360699157)
            ·
              refine ⟨46274369441810641907773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 987186548091960360699157 46274369441810641907773)
              ·
                rfl

theorem cell20_912455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 6].length) (baseStart_912455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912455 prefixEnd_912455 := by exact prefixLift 912455
  have htrace : WordTrace (prefixWord ++ tailWord_912455) baseStart_912455 baseEnd_912455 := by
    simpa [prefixWord, tailWord_912455, baseEnd_912455] using wordTrace_append hprefix tailTrace_912455
  have hstable : (prefixWord ++ tailWord_912455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912455).length < 2 ^ (prefixWord ++ tailWord_912455).sum := by decide
  have hdescent : baseEnd_912455 < baseStart_912455 := by decide
  rcases family_descends (prefixWord ++ tailWord_912455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912461 : List Nat := [1, 6, 1, 1, 1, 3, 3, 2, 2]
def baseStart_912461 : Nat := 118140960795 + 912461 * 2 ^ 59
def prefixEnd_912461 : Nat := 4983230072969 + 3 ^ 40 * 912461 * 2
def baseEnd_912461 : Nat := 416472063539786422969933

theorem tailTrace_912461 : CollatzResearch.WordTrace tailWord_912461 prefixEnd_912461 416472063539786422969933 := by
  unfold tailWord_912461
  simp only [CollatzResearch.WordTrace]
  refine ⟨33280186747317107777177237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22186791164878071851451491 33280186747317107777177237)
  ·
    refine ⟨1560008753780489427055183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33280186747317107777177237 1560008753780489427055183)
    ·
      refine ⟨2340013130670734140582775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1560008753780489427055183 2340013130670734140582775)
      ·
        refine ⟨3510019696006101210874163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2340013130670734140582775 3510019696006101210874163)
        ·
          refine ⟨5265029544009151816311245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3510019696006101210874163 5265029544009151816311245)
          ·
            refine ⟨1974386079003431931116717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5265029544009151816311245 1974386079003431931116717)
            ·
              refine ⟨740394779626286974168769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1974386079003431931116717 740394779626286974168769)
              ·
                refine ⟨555296084719715230626577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740394779626286974168769 555296084719715230626577)
                ·
                  refine ⟨416472063539786422969933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555296084719715230626577 416472063539786422969933)
                  ·
                    rfl

theorem cell20_912461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_912461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912461 prefixEnd_912461 := by exact prefixLift 912461
  have htrace : WordTrace (prefixWord ++ tailWord_912461) baseStart_912461 baseEnd_912461 := by
    simpa [prefixWord, tailWord_912461, baseEnd_912461] using wordTrace_append hprefix tailTrace_912461
  have hstable : (prefixWord ++ tailWord_912461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912461).length < 2 ^ (prefixWord ++ tailWord_912461).sum := by decide
  have hdescent : baseEnd_912461 < baseStart_912461 := by decide
  rcases family_descends (prefixWord ++ tailWord_912461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912462 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_912462 : Nat := 118140960795 + 912462 * 2 ^ 59
def prefixEnd_912462 : Nat := 4983230072969 + 3 ^ 40 * 912462 * 2
def baseEnd_912462 : Nat := 416472519967034863936595

theorem tailTrace_912462 : CollatzResearch.WordTrace tailWord_912462 prefixEnd_912462 416472519967034863936595 := by
  unfold tailWord_912462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4160027902539185618495455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22186815480208989965309093 4160027902539185618495455)
  ·
    refine ⟨6240041853808778427743183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4160027902539185618495455 6240041853808778427743183)
    ·
      refine ⟨9360062780713167641614775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6240041853808778427743183 9360062780713167641614775)
      ·
        refine ⟨14040094171069751462422163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9360062780713167641614775 14040094171069751462422163)
        ·
          refine ⟨21060141256604627193633245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14040094171069751462422163 21060141256604627193633245)
          ·
            refine ⟨7897552971226735197612467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21060141256604627193633245 7897552971226735197612467)
            ·
              refine ⟨11846329456840102796418701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7897552971226735197612467 11846329456840102796418701)
              ·
                refine ⟨4442373546315038548657013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11846329456840102796418701 4442373546315038548657013)
                ·
                  refine ⟨416472519967034863936595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4442373546315038548657013 416472519967034863936595)
                  ·
                    rfl

theorem cell20_912462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_912462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912462 prefixEnd_912462 := by exact prefixLift 912462
  have htrace : WordTrace (prefixWord ++ tailWord_912462) baseStart_912462 baseEnd_912462 := by
    simpa [prefixWord, tailWord_912462, baseEnd_912462] using wordTrace_append hprefix tailTrace_912462
  have hstable : (prefixWord ++ tailWord_912462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912462).length < 2 ^ (prefixWord ++ tailWord_912462).sum := by decide
  have hdescent : baseEnd_912462 < baseStart_912462 := by decide
  rcases family_descends (prefixWord ++ tailWord_912462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912493 : List Nat := [1, 5, 1, 1, 2, 2, 2, 6]
def baseStart_912493 : Nat := 118140960795 + 912493 * 2 ^ 59
def prefixEnd_912493 : Nat := 4983230072969 + 3 ^ 40 * 912493 * 2
def baseEnd_912493 : Nat := 138828889737245511301045

theorem tailTrace_912493 : CollatzResearch.WordTrace tailWord_912493 prefixEnd_912493 138828889737245511301045 := by
  unfold tailWord_912493
  simp only [CollatzResearch.WordTrace]
  refine ⟨33281353883201177242342133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22187569255467451494894755 33281353883201177242342133)
  ·
    refine ⟨3120126926550110366469575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33281353883201177242342133 3120126926550110366469575)
    ·
      refine ⟨4680190389825165549704363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3120126926550110366469575 4680190389825165549704363)
      ·
        refine ⟨7020285584737748324556545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4680190389825165549704363 7020285584737748324556545)
        ·
          refine ⟨5265214188553311243417409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7020285584737748324556545 5265214188553311243417409)
          ·
            refine ⟨3948910641414983432563057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5265214188553311243417409 3948910641414983432563057)
            ·
              refine ⟨2961682981061237574422293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3948910641414983432563057 2961682981061237574422293)
              ·
                refine ⟨138828889737245511301045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2961682981061237574422293 138828889737245511301045)
                ·
                  rfl

theorem cell20_912493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 6].length) (baseStart_912493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912493 prefixEnd_912493 := by exact prefixLift 912493
  have htrace : WordTrace (prefixWord ++ tailWord_912493) baseStart_912493 baseEnd_912493 := by
    simpa [prefixWord, tailWord_912493, baseEnd_912493] using wordTrace_append hprefix tailTrace_912493
  have hstable : (prefixWord ++ tailWord_912493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912493).length < 2 ^ (prefixWord ++ tailWord_912493).sum := by decide
  have hdescent : baseEnd_912493 < baseStart_912493 := by decide
  rcases family_descends (prefixWord ++ tailWord_912493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912520 : List Nat := [2, 1, 3, 4, 2, 1, 1, 4, 2]
def baseStart_912520 : Nat := 118140960795 + 912520 * 2 ^ 59
def prefixEnd_912520 : Nat := 4983230072969 + 3 ^ 40 * 912520 * 2
def baseEnd_912520 : Nat := 416498992747444440003025

theorem tailTrace_912520 : CollatzResearch.WordTrace tailWord_912520 prefixEnd_912520 416498992747444440003025 := by
  unfold tailWord_912520
  simp only [CollatzResearch.WordTrace]
  refine ⟨16641169327051680426787507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22188225769402240569050009 16641169327051680426787507)
  ·
    refine ⟨24961753990577520640181261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16641169327051680426787507 24961753990577520640181261)
    ·
      refine ⟨9360657746466570240067973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24961753990577520640181261 9360657746466570240067973)
      ·
        refine ⟨1755123327462481920012745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9360657746466570240067973 1755123327462481920012745)
        ·
          refine ⟨1316342495596861440009559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1755123327462481920012745 1316342495596861440009559)
          ·
            refine ⟨1974513743395292160014339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316342495596861440009559 1974513743395292160014339)
            ·
              refine ⟨2961770615092938240021509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1974513743395292160014339 2961770615092938240021509)
              ·
                refine ⟨555331990329925920004033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2961770615092938240021509 555331990329925920004033)
                ·
                  refine ⟨416498992747444440003025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555331990329925920004033 416498992747444440003025)
                  ·
                    rfl

theorem cell20_912520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 2].length) (baseStart_912520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912520 prefixEnd_912520 := by exact prefixLift 912520
  have htrace : WordTrace (prefixWord ++ tailWord_912520) baseStart_912520 baseEnd_912520 := by
    simpa [prefixWord, tailWord_912520, baseEnd_912520] using wordTrace_append hprefix tailTrace_912520
  have hstable : (prefixWord ++ tailWord_912520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912520).length < 2 ^ (prefixWord ++ tailWord_912520).sum := by decide
  have hdescent : baseEnd_912520 < baseStart_912520 := by decide
  rcases family_descends (prefixWord ++ tailWord_912520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912548 : List Nat := [2, 3, 1, 2, 3, 2, 3, 4]
def baseStart_912548 : Nat := 118140960795 + 912548 * 2 ^ 59
def prefixEnd_912548 : Nat := 4983230072969 + 3 ^ 40 * 912548 * 2
def baseEnd_912548 : Nat := 138837257570133595689859

theorem tailTrace_912548 : CollatzResearch.WordTrace tailWord_912548 prefixEnd_912548 138837257570133595689859 := by
  unfold tailWord_912548
  simp only [CollatzResearch.WordTrace]
  refine ⟨16641679949000960817797149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22188906598667947757062865 16641679949000960817797149)
  ·
    refine ⟨6240629980875360306673931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16641679949000960817797149 6240629980875360306673931)
    ·
      refine ⟨9360944971313040460010897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6240629980875360306673931 9360944971313040460010897)
      ·
        refine ⟨7020708728484780345008173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9360944971313040460010897 7020708728484780345008173)
        ·
          refine ⟨2632765773181792629378065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7020708728484780345008173 2632765773181792629378065)
          ·
            refine ⟨1974574329886344472033549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2632765773181792629378065 1974574329886344472033549)
            ·
              refine ⟨740465373707379177012581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1974574329886344472033549 740465373707379177012581)
              ·
                refine ⟨138837257570133595689859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 740465373707379177012581 138837257570133595689859)
                ·
                  rfl

theorem cell20_912548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_912548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912548 prefixEnd_912548 := by exact prefixLift 912548
  have htrace : WordTrace (prefixWord ++ tailWord_912548) baseStart_912548 baseEnd_912548 := by
    simpa [prefixWord, tailWord_912548, baseEnd_912548] using wordTrace_append hprefix tailTrace_912548
  have hstable : (prefixWord ++ tailWord_912548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912548).length < 2 ^ (prefixWord ++ tailWord_912548).sum := by decide
  have hdescent : baseEnd_912548 < baseStart_912548 := by decide
  rcases family_descends (prefixWord ++ tailWord_912548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912572 : List Nat := [2, 2, 2, 3, 2, 3, 1, 2, 3]
def baseStart_912572 : Nat := 118140960795 + 912572 * 2 ^ 59
def prefixEnd_912572 : Nat := 4983230072969 + 3 ^ 40 * 912572 * 2
def baseEnd_912572 : Nat := 416522726964363370269479

theorem tailTrace_912572 : CollatzResearch.WordTrace tailWord_912572 prefixEnd_912572 416522726964363370269479 := by
  unfold tailWord_912572
  simp only [CollatzResearch.WordTrace]
  refine ⟨16642117624957486867233985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22189490166609982489645313 16642117624957486867233985)
  ·
    refine ⟨12481588218718115150425489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16642117624957486867233985 12481588218718115150425489)
    ·
      refine ⟨9361191164038586362819117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12481588218718115150425489 9361191164038586362819117)
      ·
        refine ⟨3510446686514469886057169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9361191164038586362819117 3510446686514469886057169)
        ·
          refine ⟨2632835014885852414542877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3510446686514469886057169 2632835014885852414542877)
          ·
            refine ⟨987313130582194655453579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2632835014885852414542877 987313130582194655453579)
            ·
              refine ⟨1480969695873291983180369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987313130582194655453579 1480969695873291983180369)
              ·
                refine ⟨1110727271904968987385277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480969695873291983180369 1110727271904968987385277)
                ·
                  refine ⟨416522726964363370269479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1110727271904968987385277 416522726964363370269479)
                  ·
                    rfl

theorem cell20_912572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_912572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912572 prefixEnd_912572 := by exact prefixLift 912572
  have htrace : WordTrace (prefixWord ++ tailWord_912572) baseStart_912572 baseEnd_912572 := by
    simpa [prefixWord, tailWord_912572, baseEnd_912572] using wordTrace_append hprefix tailTrace_912572
  have hstable : (prefixWord ++ tailWord_912572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912572).length < 2 ^ (prefixWord ++ tailWord_912572).sum := by decide
  have hdescent : baseEnd_912572 < baseStart_912572 := by decide
  rcases family_descends (prefixWord ++ tailWord_912572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912607 : List Nat := [1, 1, 2, 3, 2, 1, 6, 4]
def baseStart_912607 : Nat := 118140960795 + 912607 * 2 ^ 59
def prefixEnd_912607 : Nat := 4983230072969 + 3 ^ 40 * 912607 * 2
def baseEnd_912607 : Nat := 138846233972686268034223

theorem tailTrace_912607 : CollatzResearch.WordTrace tailWord_912607 prefixEnd_912607 138846233972686268034223 := by
  unfold tailWord_912607
  simp only [CollatzResearch.WordTrace]
  refine ⟨33285511804788174711992075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22190341203192116474661383 33285511804788174711992075)
  ·
    refine ⟨49928267707182262067988113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33285511804788174711992075 49928267707182262067988113)
    ·
      refine ⟨37446200780386696550991085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49928267707182262067988113 37446200780386696550991085)
      ·
        refine ⟨14042325292645011206621657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37446200780386696550991085 14042325292645011206621657)
        ·
          refine ⟨10531743969483758404966243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14042325292645011206621657 10531743969483758404966243)
          ·
            refine ⟨15797615954225637607449365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10531743969483758404966243 15797615954225637607449365)
            ·
              refine ⟨740513247854326762849189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15797615954225637607449365 740513247854326762849189)
              ·
                refine ⟨138846233972686268034223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 740513247854326762849189 138846233972686268034223)
                ·
                  rfl

theorem cell20_912607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 4].length) (baseStart_912607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912607 prefixEnd_912607 := by exact prefixLift 912607
  have htrace : WordTrace (prefixWord ++ tailWord_912607) baseStart_912607 baseEnd_912607 := by
    simpa [prefixWord, tailWord_912607, baseEnd_912607] using wordTrace_append hprefix tailTrace_912607
  have hstable : (prefixWord ++ tailWord_912607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912607).length < 2 ^ (prefixWord ++ tailWord_912607).sum := by decide
  have hdescent : baseEnd_912607 < baseStart_912607 := by decide
  rcases family_descends (prefixWord ++ tailWord_912607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912613 : List Nat := [1, 3, 1, 4, 4, 1, 1, 3, 2]
def baseStart_912613 : Nat := 118140960795 + 912613 * 2 ^ 59
def prefixEnd_912613 : Nat := 4983230072969 + 3 ^ 40 * 912613 * 2
def baseEnd_912613 : Nat := 416541440481549449902645

theorem tailTrace_912613 : CollatzResearch.WordTrace tailWord_912613 prefixEnd_912613 416541440481549449902645 := by
  unfold tailWord_912613
  simp only [CollatzResearch.WordTrace]
  refine ⟨33285730642766437736710493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22190487095177625157806995 33285730642766437736710493)
  ·
    refine ⟨12482148991037414151266435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33285730642766437736710493 12482148991037414151266435)
    ·
      refine ⟨18723223486556121226899653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12482148991037414151266435 18723223486556121226899653)
      ·
        refine ⟨3510604403729272730043685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18723223486556121226899653 3510604403729272730043685)
        ·
          refine ⟨658238325699238636883191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3510604403729272730043685 658238325699238636883191)
          ·
            refine ⟨987357488548857955324787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658238325699238636883191 987357488548857955324787)
            ·
              refine ⟨1481036232823286932987181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987357488548857955324787 1481036232823286932987181)
              ·
                refine ⟨555388587308732599870193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1481036232823286932987181 555388587308732599870193)
                ·
                  refine ⟨416541440481549449902645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555388587308732599870193 416541440481549449902645)
                  ·
                    rfl

theorem cell20_912613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_912613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912613 prefixEnd_912613 := by exact prefixLift 912613
  have htrace : WordTrace (prefixWord ++ tailWord_912613) baseStart_912613 baseEnd_912613 := by
    simpa [prefixWord, tailWord_912613, baseEnd_912613] using wordTrace_append hprefix tailTrace_912613
  have hstable : (prefixWord ++ tailWord_912613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912613).length < 2 ^ (prefixWord ++ tailWord_912613).sum := by decide
  have hdescent : baseEnd_912613 < baseStart_912613 := by decide
  rcases family_descends (prefixWord ++ tailWord_912613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912693 : List Nat := [1, 3, 3, 1, 2, 3, 1, 4, 2]
def baseStart_912693 : Nat := 118140960795 + 912693 * 2 ^ 59
def prefixEnd_912693 : Nat := 4983230072969 + 3 ^ 40 * 912693 * 2
def baseEnd_912693 : Nat := 416577954661424727235651

theorem tailTrace_912693 : CollatzResearch.WordTrace tailWord_912693 prefixEnd_912693 416577954661424727235651 := by
  unfold tailWord_912693
  simp only [CollatzResearch.WordTrace]
  refine ⟨33288648482476611399622733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22192432321651074266415155 33288648482476611399622733)
  ·
    refine ⟨12483243180928729274858525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33288648482476611399622733 12483243180928729274858525)
    ·
      refine ⟨4681216192848273478071947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12483243180928729274858525 4681216192848273478071947)
      ·
        refine ⟨7021824289272410217107921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4681216192848273478071947 7021824289272410217107921)
        ·
          refine ⟨5266368216954307662830941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7021824289272410217107921 5266368216954307662830941)
          ·
            refine ⟨1974888081357865373561603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5266368216954307662830941 1974888081357865373561603)
            ·
              refine ⟨2962332122036798060342405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1974888081357865373561603 2962332122036798060342405)
              ·
                refine ⟨555437272881899636314201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2962332122036798060342405 555437272881899636314201)
                ·
                  refine ⟨416577954661424727235651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555437272881899636314201 416577954661424727235651)
                  ·
                    rfl

theorem cell20_912693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_912693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912693 prefixEnd_912693 := by exact prefixLift 912693
  have htrace : WordTrace (prefixWord ++ tailWord_912693) baseStart_912693 baseEnd_912693 := by
    simpa [prefixWord, tailWord_912693, baseEnd_912693] using wordTrace_append hprefix tailTrace_912693
  have hstable : (prefixWord ++ tailWord_912693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912693).length < 2 ^ (prefixWord ++ tailWord_912693).sum := by decide
  have hdescent : baseEnd_912693 < baseStart_912693 := by decide
  rcases family_descends (prefixWord ++ tailWord_912693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912721 : List Nat := [1, 2, 2, 1, 4, 1, 5, 4]
def baseStart_912721 : Nat := 118140960795 + 912721 * 2 ^ 59
def prefixEnd_912721 : Nat := 4983230072969 + 3 ^ 40 * 912721 * 2
def baseEnd_912721 : Nat := 138863578208127024767401

theorem tailTrace_912721 : CollatzResearch.WordTrace tailWord_912721 prefixEnd_912721 138863578208127024767401 := by
  unfold tailWord_912721
  simp only [CollatzResearch.WordTrace]
  refine ⟨33289669726375172181642017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22193113150916781454428011 33289669726375172181642017)
  ·
    refine ⟨24967252294781379136231513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33289669726375172181642017 24967252294781379136231513)
    ·
      refine ⟨18725439221086034352173635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24967252294781379136231513 18725439221086034352173635)
      ·
        refine ⟨28088158831629051528260453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18725439221086034352173635 28088158831629051528260453)
        ·
          refine ⟨5266529780930447161548835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28088158831629051528260453 5266529780930447161548835)
          ·
            refine ⟨7899794671395670742323253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5266529780930447161548835 7899794671395670742323253)
            ·
              refine ⟨740605750443344132092805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7899794671395670742323253 740605750443344132092805)
              ·
                refine ⟨138863578208127024767401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 740605750443344132092805 138863578208127024767401)
                ·
                  rfl

theorem cell20_912721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 4].length) (baseStart_912721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912721 prefixEnd_912721 := by exact prefixLift 912721
  have htrace : WordTrace (prefixWord ++ tailWord_912721) baseStart_912721 baseEnd_912721 := by
    simpa [prefixWord, tailWord_912721, baseEnd_912721] using wordTrace_append hprefix tailTrace_912721
  have hstable : (prefixWord ++ tailWord_912721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912721).length < 2 ^ (prefixWord ++ tailWord_912721).sum := by decide
  have hdescent : baseEnd_912721 < baseStart_912721 := by decide
  rcases family_descends (prefixWord ++ tailWord_912721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912752 : List Nat := [2, 1, 1, 1, 4, 2, 1, 6, 2]
def baseStart_912752 : Nat := 118140960795 + 912752 * 2 ^ 59
def prefixEnd_912752 : Nat := 4983230072969 + 3 ^ 40 * 912752 * 2
def baseEnd_912752 : Nat := 416604883869082744268743

theorem tailTrace_912752 : CollatzResearch.WordTrace tailWord_912752 prefixEnd_912752 416604883869082744268743 := by
  unfold tailWord_912752
  simp only [CollatzResearch.WordTrace]
  refine ⟨16645400194631432238010255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22193866926175242984013673 16645400194631432238010255)
  ·
    refine ⟨24968100291947148357015383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16645400194631432238010255 24968100291947148357015383)
    ·
      refine ⟨37452150437920722535523075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24968100291947148357015383 37452150437920722535523075)
      ·
        refine ⟨56178225656881083803284613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37452150437920722535523075 56178225656881083803284613)
        ·
          refine ⟨10533417310665203213115865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56178225656881083803284613 10533417310665203213115865)
          ·
            refine ⟨7900062982998902409836899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10533417310665203213115865 7900062982998902409836899)
            ·
              refine ⟨11850094474498353614755349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7900062982998902409836899 11850094474498353614755349)
              ·
                refine ⟨555473178492110325691657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11850094474498353614755349 555473178492110325691657)
                ·
                  refine ⟨416604883869082744268743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555473178492110325691657 416604883869082744268743)
                  ·
                    rfl

theorem cell20_912752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 2].length) (baseStart_912752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912752 prefixEnd_912752 := by exact prefixLift 912752
  have htrace : WordTrace (prefixWord ++ tailWord_912752) baseStart_912752 baseEnd_912752 := by
    simpa [prefixWord, tailWord_912752, baseEnd_912752] using wordTrace_append hprefix tailTrace_912752
  have hstable : (prefixWord ++ tailWord_912752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912752).length < 2 ^ (prefixWord ++ tailWord_912752).sum := by decide
  have hdescent : baseEnd_912752 < baseStart_912752 := by decide
  rcases family_descends (prefixWord ++ tailWord_912752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912773 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 4]
def baseStart_912773 : Nat := 118140960795 + 912773 * 2 ^ 59
def prefixEnd_912773 : Nat := 4983230072969 + 3 ^ 40 * 912773 * 2
def baseEnd_912773 : Nat := 416614468841300004568657

theorem tailTrace_912773 : CollatzResearch.WordTrace tailWord_912773 prefixEnd_912773 416614468841300004568657 := by
  unfold tailWord_912773
  simp only [CollatzResearch.WordTrace]
  refine ⟨33291566322186785062534973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22194377548124523375023315 33291566322186785062534973)
  ·
    refine ⟨12484337370820044398450615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33291566322186785062534973 12484337370820044398450615)
    ·
      refine ⟨18726506056230066597675923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12484337370820044398450615 18726506056230066597675923)
      ·
        refine ⟨28089759084345099896513885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18726506056230066597675923 28089759084345099896513885)
        ·
          refine ⟨10533659656629412461192707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28089759084345099896513885 10533659656629412461192707)
          ·
            refine ⟨15800489484944118691789061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10533659656629412461192707 15800489484944118691789061)
            ·
              refine ⟨2962591778427022254710449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15800489484944118691789061 2962591778427022254710449)
              ·
                refine ⟨2221943833820266691032837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2962591778427022254710449 2221943833820266691032837)
                ·
                  refine ⟨416614468841300004568657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2221943833820266691032837 416614468841300004568657)
                  ·
                    rfl

theorem cell20_912773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_912773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912773 prefixEnd_912773 := by exact prefixLift 912773
  have htrace : WordTrace (prefixWord ++ tailWord_912773) baseStart_912773 baseEnd_912773 := by
    simpa [prefixWord, tailWord_912773, baseEnd_912773] using wordTrace_append hprefix tailTrace_912773
  have hstable : (prefixWord ++ tailWord_912773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912773).length < 2 ^ (prefixWord ++ tailWord_912773).sum := by decide
  have hdescent : baseEnd_912773 < baseStart_912773 := by decide
  rcases family_descends (prefixWord ++ tailWord_912773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912776 : List Nat := [2, 1, 3, 3, 1, 4, 2, 4]
def baseStart_912776 : Nat := 118140960795 + 912776 * 2 ^ 59
def prefixEnd_912776 : Nat := 4983230072969 + 3 ^ 40 * 912776 * 2
def baseEnd_912776 : Nat := 138871946041015109156215

theorem tailTrace_912776 : CollatzResearch.WordTrace tailWord_912776 prefixEnd_912776 138871946041015109156215 := by
  unfold tailWord_912776
  simp only [CollatzResearch.WordTrace]
  refine ⟨16645837870587958287447091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22194450494117277716596121 16645837870587958287447091)
  ·
    refine ⟨24968756805881937431170637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16645837870587958287447091 24968756805881937431170637)
    ·
      refine ⟨9363283802205726536688989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24968756805881937431170637 9363283802205726536688989)
      ·
        refine ⟨3511231425827147451258371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9363283802205726536688989 3511231425827147451258371)
        ·
          refine ⟨5266847138740721176887557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3511231425827147451258371 5266847138740721176887557)
          ·
            refine ⟨987533838513885220666417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5266847138740721176887557 987533838513885220666417)
            ·
              refine ⟨740650378885413915499813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 987533838513885220666417 740650378885413915499813)
              ·
                refine ⟨138871946041015109156215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 740650378885413915499813 138871946041015109156215)
                ·
                  rfl

theorem cell20_912776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_912776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912776 prefixEnd_912776 := by exact prefixLift 912776
  have htrace : WordTrace (prefixWord ++ tailWord_912776) baseStart_912776 baseEnd_912776 := by
    simpa [prefixWord, tailWord_912776, baseEnd_912776] using wordTrace_append hprefix tailTrace_912776
  have hstable : (prefixWord ++ tailWord_912776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912776).length < 2 ^ (prefixWord ++ tailWord_912776).sum := by decide
  have hdescent : baseEnd_912776 < baseStart_912776 := by decide
  rcases family_descends (prefixWord ++ tailWord_912776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912780 : List Nat := [2, 2, 1, 2, 1, 3, 3, 6]
def baseStart_912780 : Nat := 118140960795 + 912780 * 2 ^ 59
def prefixEnd_912780 : Nat := 4983230072969 + 3 ^ 40 * 912780 * 2
def baseEnd_912780 : Nat := 138872554610679697111765

theorem tailTrace_912780 : CollatzResearch.WordTrace tailWord_912780 prefixEnd_912780 138872554610679697111765 := by
  unfold tailWord_912780
  simp only [CollatzResearch.WordTrace]
  refine ⟨16645910816580712629019897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22194547755440950172026529 16645910816580712629019897)
  ·
    refine ⟨12484433112435534471764923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16645910816580712629019897 12484433112435534471764923)
    ·
      refine ⟨18726649668653301707647385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12484433112435534471764923 18726649668653301707647385)
      ·
        refine ⟨14044987251489976280735539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18726649668653301707647385 14044987251489976280735539)
        ·
          refine ⟨21067480877234964421103309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14044987251489976280735539 21067480877234964421103309)
          ·
            refine ⟨7900305328963111657913741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21067480877234964421103309 7900305328963111657913741)
            ·
              refine ⟨2962614498361166871717653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7900305328963111657913741 2962614498361166871717653)
              ·
                refine ⟨138872554610679697111765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2962614498361166871717653 138872554610679697111765)
                ·
                  rfl

theorem cell20_912780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_912780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912780 prefixEnd_912780 := by exact prefixLift 912780
  have htrace : WordTrace (prefixWord ++ tailWord_912780) baseStart_912780 baseEnd_912780 := by
    simpa [prefixWord, tailWord_912780, baseEnd_912780] using wordTrace_append hprefix tailTrace_912780
  have hstable : (prefixWord ++ tailWord_912780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912780).length < 2 ^ (prefixWord ++ tailWord_912780).sum := by decide
  have hdescent : baseEnd_912780 < baseStart_912780 := by decide
  rcases family_descends (prefixWord ++ tailWord_912780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912797 : List Nat := [1, 4, 2, 1, 3, 3, 6]
def baseStart_912797 : Nat := 118140960795 + 912797 * 2 ^ 59
def prefixEnd_912797 : Nat := 4983230072969 + 3 ^ 40 * 912797 * 2
def baseEnd_912797 : Nat := 46291713677251398640951

theorem tailTrace_912797 : CollatzResearch.WordTrace tailWord_912797 prefixEnd_912797 46291713677251398640951 := by
  unfold tailWord_912797
  simp only [CollatzResearch.WordTrace]
  refine ⟨33292441674099837161408645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22194961116066558107605763 33292441674099837161408645)
  ·
    refine ⟨6242332813893719467764121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33292441674099837161408645 6242332813893719467764121)
    ·
      refine ⟨4681749610420289600823091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6242332813893719467764121 4681749610420289600823091)
      ·
        refine ⟨7022624415630434401234637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4681749610420289600823091 7022624415630434401234637)
        ·
          refine ⟨2633484155861412900462989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7022624415630434401234637 2633484155861412900462989)
          ·
            refine ⟨987556558448029837673621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2633484155861412900462989 987556558448029837673621)
            ·
              refine ⟨46291713677251398640951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 987556558448029837673621 46291713677251398640951)
              ·
                rfl

theorem cell20_912797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 6].length) (baseStart_912797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912797 prefixEnd_912797 := by exact prefixLift 912797
  have htrace : WordTrace (prefixWord ++ tailWord_912797) baseStart_912797 baseEnd_912797 := by
    simpa [prefixWord, tailWord_912797, baseEnd_912797] using wordTrace_append hprefix tailTrace_912797
  have hstable : (prefixWord ++ tailWord_912797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912797).length < 2 ^ (prefixWord ++ tailWord_912797).sum := by decide
  have hdescent : baseEnd_912797 < baseStart_912797 := by decide
  rcases family_descends (prefixWord ++ tailWord_912797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912804 : List Nat := [2, 3, 1, 2, 1, 1, 1, 6, 3]
def baseStart_912804 : Nat := 118140960795 + 912804 * 2 ^ 59
def prefixEnd_912804 : Nat := 4983230072969 + 3 ^ 40 * 912804 * 2
def baseEnd_912804 : Nat := 416628618086001674535197

theorem tailTrace_912804 : CollatzResearch.WordTrace tailWord_912804 prefixEnd_912804 416628618086001674535197 := by
  unfold tailWord_912804
  simp only [CollatzResearch.WordTrace]
  refine ⟨16646348492537238678456733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22195131323382984904608977 16646348492537238678456733)
  ·
    refine ⟨6242380684701464504421275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16646348492537238678456733 6242380684701464504421275)
    ·
      refine ⟨9363571027052196756631913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6242380684701464504421275 9363571027052196756631913)
      ·
        refine ⟨7022678270289147567473935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9363571027052196756631913 7022678270289147567473935)
        ·
          refine ⟨10534017405433721351210903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7022678270289147567473935 10534017405433721351210903)
          ·
            refine ⟨15801026108150582026816355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10534017405433721351210903 15801026108150582026816355)
            ·
              refine ⟨23701539162225873040224533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15801026108150582026816355 23701539162225873040224533)
              ·
                refine ⟨1111009648229337798760525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23701539162225873040224533 1111009648229337798760525)
                ·
                  refine ⟨416628618086001674535197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111009648229337798760525 416628618086001674535197)
                  ·
                    rfl

theorem cell20_912804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_912804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912804 prefixEnd_912804 := by exact prefixLift 912804
  have htrace : WordTrace (prefixWord ++ tailWord_912804) baseStart_912804 baseEnd_912804 := by
    simpa [prefixWord, tailWord_912804, baseEnd_912804] using wordTrace_append hprefix tailTrace_912804
  have hstable : (prefixWord ++ tailWord_912804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912804).length < 2 ^ (prefixWord ++ tailWord_912804).sum := by decide
  have hdescent : baseEnd_912804 < baseStart_912804 := by decide
  rcases family_descends (prefixWord ++ tailWord_912804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912821 : List Nat := [1, 3, 3, 2, 2, 2, 1, 3, 3]
def baseStart_912821 : Nat := 118140960795 + 912821 * 2 ^ 59
def prefixEnd_912821 : Nat := 4983230072969 + 3 ^ 40 * 912821 * 2
def baseEnd_912821 : Nat := 416636377349225170968461

theorem tailTrace_912821 : CollatzResearch.WordTrace tailWord_912821 prefixEnd_912821 416636377349225170968461 := by
  unfold tailWord_912821
  simp only [CollatzResearch.WordTrace]
  refine ⟨33293317026012889260282317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22195544684008592840188211 33293317026012889260282317)
  ·
    refine ⟨12484993884754833472605869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33293317026012889260282317 12484993884754833472605869)
    ·
      refine ⟨4681872706783062552227201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12484993884754833472605869 4681872706783062552227201)
      ·
        refine ⟨3511404530087296914170401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4681872706783062552227201 3511404530087296914170401)
        ·
          refine ⟨2633553397565472685627801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3511404530087296914170401 2633553397565472685627801)
          ·
            refine ⟨1975165048174104514220851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2633553397565472685627801 1975165048174104514220851)
            ·
              refine ⟨2962747572261156771331277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1975165048174104514220851 2962747572261156771331277)
              ·
                refine ⟨1111030339597933789249229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2962747572261156771331277 1111030339597933789249229)
                ·
                  refine ⟨416636377349225170968461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111030339597933789249229 416636377349225170968461)
                  ·
                    rfl

theorem cell20_912821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_912821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912821 prefixEnd_912821 := by exact prefixLift 912821
  have htrace : WordTrace (prefixWord ++ tailWord_912821) baseStart_912821 baseEnd_912821 := by
    simpa [prefixWord, tailWord_912821, baseEnd_912821] using wordTrace_append hprefix tailTrace_912821
  have hstable : (prefixWord ++ tailWord_912821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912821).length < 2 ^ (prefixWord ++ tailWord_912821).sum := by decide
  have hdescent : baseEnd_912821 < baseStart_912821 := by decide
  rcases family_descends (prefixWord ++ tailWord_912821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912880 : List Nat := [2, 1, 1, 1, 3, 4, 2, 3, 3]
def baseStart_912880 : Nat := 118140960795 + 912880 * 2 ^ 59
def prefixEnd_912880 : Nat := 4983230072969 + 3 ^ 40 * 912880 * 2
def baseEnd_912880 : Nat := 416663306556883188001553

theorem tailTrace_912880 : CollatzResearch.WordTrace tailWord_912880 prefixEnd_912880 416663306556883188001553 := by
  unfold tailWord_912880
  simp only [CollatzResearch.WordTrace]
  refine ⟨16647734466399571168340047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22196979288532761557786729 16647734466399571168340047)
  ·
    refine ⟨24971601699599356752510071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16647734466399571168340047 24971601699599356752510071)
    ·
      refine ⟨37457402549399035128765107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24971601699599356752510071 37457402549399035128765107)
      ·
        refine ⟨56186103824098552693147661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37457402549399035128765107 56186103824098552693147661)
        ·
          refine ⟨21069788934036957259930373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56186103824098552693147661 21069788934036957259930373)
          ·
            refine ⟨3950585425131929486236945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21069788934036957259930373 3950585425131929486236945)
            ·
              refine ⟨2962939068848947114677709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3950585425131929486236945 2962939068848947114677709)
              ·
                refine ⟨1111102150818355168004141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2962939068848947114677709 1111102150818355168004141)
                ·
                  refine ⟨416663306556883188001553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111102150818355168004141 416663306556883188001553)
                  ·
                    rfl

theorem cell20_912880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_912880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912880 prefixEnd_912880 := by exact prefixLift 912880
  have htrace : WordTrace (prefixWord ++ tailWord_912880) baseStart_912880 baseEnd_912880 := by
    simpa [prefixWord, tailWord_912880, baseEnd_912880] using wordTrace_append hprefix tailTrace_912880
  have hstable : (prefixWord ++ tailWord_912880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912880).length < 2 ^ (prefixWord ++ tailWord_912880).sum := by decide
  have hdescent : baseEnd_912880 < baseStart_912880 := by decide
  rcases family_descends (prefixWord ++ tailWord_912880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912900 : List Nat := [2, 3, 2, 3, 2, 1, 2, 3, 2]
def baseStart_912900 : Nat := 118140960795 + 912900 * 2 ^ 59
def prefixEnd_912900 : Nat := 4983230072969 + 3 ^ 40 * 912900 * 2
def baseEnd_912900 : Nat := 416672435101852007334805

theorem tailTrace_912900 : CollatzResearch.WordTrace tailWord_912900 prefixEnd_912900 416672435101852007334805 := by
  unfold tailWord_912900
  simp only [CollatzResearch.WordTrace]
  refine ⟨16648099196363342876204077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22197465595151123834938769 16648099196363342876204077)
  ·
    refine ⟨6243037198636253578576529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16648099196363342876204077 6243037198636253578576529)
    ·
      refine ⟨4682277898977190183932397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6243037198636253578576529 4682277898977190183932397)
      ·
        refine ⟨1755854212116446318974649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4682277898977190183932397 1755854212116446318974649)
        ·
          refine ⟨1316890659087334739230987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1755854212116446318974649 1316890659087334739230987)
          ·
            refine ⟨1975335988631002108846481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316890659087334739230987 1975335988631002108846481)
            ·
              refine ⟨1481501991473251581634861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1975335988631002108846481 1481501991473251581634861)
              ·
                refine ⟨555563246802469343113073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1481501991473251581634861 555563246802469343113073)
                ·
                  refine ⟨416672435101852007334805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555563246802469343113073 416672435101852007334805)
                  ·
                    rfl

theorem cell20_912900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_912900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912900 prefixEnd_912900 := by exact prefixLift 912900
  have htrace : WordTrace (prefixWord ++ tailWord_912900) baseStart_912900 baseEnd_912900 := by
    simpa [prefixWord, tailWord_912900, baseEnd_912900] using wordTrace_append hprefix tailTrace_912900
  have hstable : (prefixWord ++ tailWord_912900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912900).length < 2 ^ (prefixWord ++ tailWord_912900).sum := by decide
  have hdescent : baseEnd_912900 < baseStart_912900 := by decide
  rcases family_descends (prefixWord ++ tailWord_912900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912901 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 5]
def baseStart_912901 : Nat := 118140960795 + 912901 * 2 ^ 59
def prefixEnd_912901 : Nat := 4983230072969 + 3 ^ 40 * 912901 * 2
def baseEnd_912901 : Nat := 416672891529100448301467

theorem tailTrace_912901 : CollatzResearch.WordTrace tailWord_912901 prefixEnd_912901 416672891529100448301467 := by
  unfold tailWord_912901
  simp only [CollatzResearch.WordTrace]
  refine ⟨33296234865723062923194557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22197489910482041948796371 33296234865723062923194557)
  ·
    refine ⟨12486088074646148596197959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33296234865723062923194557 12486088074646148596197959)
    ·
      refine ⟨18729132111969222894296939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12486088074646148596197959 18729132111969222894296939)
      ·
        refine ⟨28093698167953834341445409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18729132111969222894296939 28093698167953834341445409)
        ·
          refine ⟨21070273625965375756084057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28093698167953834341445409 21070273625965375756084057)
          ·
            refine ⟨15802705219474031817063043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21070273625965375756084057 15802705219474031817063043)
            ·
              refine ⟨23704057829211047725594565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15802705219474031817063043 23704057829211047725594565)
              ·
                refine ⟨4444510842977071448548981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23704057829211047725594565 4444510842977071448548981)
                ·
                  refine ⟨416672891529100448301467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4444510842977071448548981 416672891529100448301467)
                  ·
                    rfl

theorem cell20_912901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_912901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912901 prefixEnd_912901 := by exact prefixLift 912901
  have htrace : WordTrace (prefixWord ++ tailWord_912901) baseStart_912901 baseEnd_912901 := by
    simpa [prefixWord, tailWord_912901, baseEnd_912901] using wordTrace_append hprefix tailTrace_912901
  have hstable : (prefixWord ++ tailWord_912901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912901).length < 2 ^ (prefixWord ++ tailWord_912901).sum := by decide
  have hdescent : baseEnd_912901 < baseStart_912901 := by decide
  rcases family_descends (prefixWord ++ tailWord_912901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912904 : List Nat := [2, 1, 3, 2, 1, 1, 3, 5, 2]
def baseStart_912904 : Nat := 118140960795 + 912904 * 2 ^ 59
def prefixEnd_912904 : Nat := 4983230072969 + 3 ^ 40 * 912904 * 2
def baseEnd_912904 : Nat := 416674260810845771201455

theorem tailTrace_912904 : CollatzResearch.WordTrace tailWord_912904 prefixEnd_912904 416674260810845771201455 := by
  unfold tailWord_912904
  simp only [CollatzResearch.WordTrace]
  refine ⟨16648172142356097217776883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22197562856474796290369177 16648172142356097217776883)
  ·
    refine ⟨24972258213534145826665325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16648172142356097217776883 24972258213534145826665325)
    ·
      refine ⟨9364596830075304684999497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24972258213534145826665325 9364596830075304684999497)
      ·
        refine ⟨7023447622556478513749623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9364596830075304684999497 7023447622556478513749623)
        ·
          refine ⟨10535171433834717770624435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7023447622556478513749623 10535171433834717770624435)
          ·
            refine ⟨15802757150752076655936653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10535171433834717770624435 15802757150752076655936653)
            ·
              refine ⟨5926033931532028745976245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15802757150752076655936653 5926033931532028745976245)
              ·
                refine ⟨555565681081127694935273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5926033931532028745976245 555565681081127694935273)
                ·
                  refine ⟨416674260810845771201455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555565681081127694935273 416674260810845771201455)
                  ·
                    rfl

theorem cell20_912904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 2].length) (baseStart_912904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912904 prefixEnd_912904 := by exact prefixLift 912904
  have htrace : WordTrace (prefixWord ++ tailWord_912904) baseStart_912904 baseEnd_912904 := by
    simpa [prefixWord, tailWord_912904, baseEnd_912904] using wordTrace_append hprefix tailTrace_912904
  have hstable : (prefixWord ++ tailWord_912904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912904).length < 2 ^ (prefixWord ++ tailWord_912904).sum := by decide
  have hdescent : baseEnd_912904 < baseStart_912904 := by decide
  rcases family_descends (prefixWord ++ tailWord_912904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912942 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_912942 : Nat := 118140960795 + 912942 * 2 ^ 59
def prefixEnd_912942 : Nat := 4983230072969 + 3 ^ 40 * 912942 * 2
def baseEnd_912942 : Nat := 416691605046286527934633

theorem tailTrace_912942 : CollatzResearch.WordTrace tailWord_912942 prefixEnd_912942 416691605046286527934633 := by
  unfold tailWord_912942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4162216282321815865679635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22198486839049684616958053 4162216282321815865679635)
  ·
    refine ⟨6243324423482723798519453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4162216282321815865679635 6243324423482723798519453)
    ·
      refine ⟨2341246658806021424444795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6243324423482723798519453 2341246658806021424444795)
      ·
        refine ⟨3511869988209032136667193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2341246658806021424444795 3511869988209032136667193)
        ·
          refine ⟨2633902491156774102500395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3511869988209032136667193 2633902491156774102500395)
          ·
            refine ⟨3950853736735161153750593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2633902491156774102500395 3950853736735161153750593)
            ·
              refine ⟨2963140302551370865312945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3950853736735161153750593 2963140302551370865312945)
              ·
                refine ⟨2222355226913528148984709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2963140302551370865312945 2222355226913528148984709)
                ·
                  refine ⟨416691605046286527934633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2222355226913528148984709 416691605046286527934633)
                  ·
                    rfl

theorem cell20_912942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_912942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912942 prefixEnd_912942 := by exact prefixLift 912942
  have htrace : WordTrace (prefixWord ++ tailWord_912942) baseStart_912942 baseEnd_912942 := by
    simpa [prefixWord, tailWord_912942, baseEnd_912942] using wordTrace_append hprefix tailTrace_912942
  have hstable : (prefixWord ++ tailWord_912942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912942).length < 2 ^ (prefixWord ++ tailWord_912942).sum := by decide
  have hdescent : baseEnd_912942 < baseStart_912942 := by decide
  rcases family_descends (prefixWord ++ tailWord_912942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912949 : List Nat := [1, 3, 3, 1, 1, 3, 4, 4]
def baseStart_912949 : Nat := 118140960795 + 912949 * 2 ^ 59
def prefixEnd_912949 : Nat := 4983230072969 + 3 ^ 40 * 912949 * 2
def baseEnd_912949 : Nat := 138898266679008538233757

theorem tailTrace_912949 : CollatzResearch.WordTrace tailWord_912949 prefixEnd_912949 138898266679008538233757 := by
  unfold tailWord_912949
  simp only [CollatzResearch.WordTrace]
  refine ⟨33297985569549167120941901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22198657046366111413961267 33297985569549167120941901)
  ·
    refine ⟨12486744588580937670353213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33297985569549167120941901 12486744588580937670353213)
    ·
      refine ⟨4682529220717851626382455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12486744588580937670353213 4682529220717851626382455)
      ·
        refine ⟨7023793831076777439573683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4682529220717851626382455 7023793831076777439573683)
        ·
          refine ⟨10535690746615166159360525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7023793831076777439573683 10535690746615166159360525)
          ·
            refine ⟨3950884029980687309760197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10535690746615166159360525 3950884029980687309760197)
            ·
              refine ⟨740790755621378870580037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3950884029980687309760197 740790755621378870580037)
              ·
                refine ⟨138898266679008538233757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 740790755621378870580037 138898266679008538233757)
                ·
                  rfl

theorem cell20_912949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 4].length) (baseStart_912949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912949 prefixEnd_912949 := by exact prefixLift 912949
  have htrace : WordTrace (prefixWord ++ tailWord_912949) baseStart_912949 baseEnd_912949 := by
    simpa [prefixWord, tailWord_912949, baseEnd_912949] using wordTrace_append hprefix tailTrace_912949
  have hstable : (prefixWord ++ tailWord_912949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912949).length < 2 ^ (prefixWord ++ tailWord_912949).sum := by decide
  have hdescent : baseEnd_912949 < baseStart_912949 := by decide
  rcases family_descends (prefixWord ++ tailWord_912949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912959 : List Nat := [1, 1, 2, 2, 3, 5, 1, 3, 2]
def baseStart_912959 : Nat := 118140960795 + 912959 * 2 ^ 59
def prefixEnd_912959 : Nat := 4983230072969 + 3 ^ 40 * 912959 * 2
def baseEnd_912959 : Nat := 416699364309510024367897

theorem tailTrace_912959 : CollatzResearch.WordTrace tailWord_912959 prefixEnd_912959 416699364309510024367897 := by
  unfold tailWord_912959
  simp only [CollatzResearch.WordTrace]
  refine ⟨33298350299512938828805931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22198900199675292552537287 33298350299512938828805931)
  ·
    refine ⟨49947525449269408243208897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33298350299512938828805931 49947525449269408243208897)
    ·
      refine ⟨37460644086952056182406673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49947525449269408243208897 37460644086952056182406673)
      ·
        refine ⟨28095483065214042136805005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37460644086952056182406673 28095483065214042136805005)
        ·
          refine ⟨10535806149455265801301877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28095483065214042136805005 10535806149455265801301877)
          ·
            refine ⟨987731826511431168872051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10535806149455265801301877 987731826511431168872051)
            ·
              refine ⟨1481597739767146753308077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987731826511431168872051 1481597739767146753308077)
              ·
                refine ⟨555599152412680032490529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1481597739767146753308077 555599152412680032490529)
                ·
                  refine ⟨416699364309510024367897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555599152412680032490529 416699364309510024367897)
                  ·
                    rfl

theorem cell20_912959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 2].length) (baseStart_912959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912959 prefixEnd_912959 := by exact prefixLift 912959
  have htrace : WordTrace (prefixWord ++ tailWord_912959) baseStart_912959 baseEnd_912959 := by
    simpa [prefixWord, tailWord_912959, baseEnd_912959] using wordTrace_append hprefix tailTrace_912959
  have hstable : (prefixWord ++ tailWord_912959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912959).length < 2 ^ (prefixWord ++ tailWord_912959).sum := by decide
  have hdescent : baseEnd_912959 < baseStart_912959 := by decide
  rcases family_descends (prefixWord ++ tailWord_912959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912977 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 5]
def baseStart_912977 : Nat := 118140960795 + 912977 * 2 ^ 59
def prefixEnd_912977 : Nat := 4983230072969 + 3 ^ 40 * 912977 * 2
def baseEnd_912977 : Nat := 416707579999981961767823

theorem tailTrace_912977 : CollatzResearch.WordTrace tailWord_912977 prefixEnd_912977 416707579999981961767823 := by
  unfold tailWord_912977
  simp only [CollatzResearch.WordTrace]
  refine ⟨33299006813447727902961185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22199337875631818601974123 33299006813447727902961185)
  ·
    refine ⟨24974255110085795927220889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33299006813447727902961185 24974255110085795927220889)
    ·
      refine ⟨18730691332564346945415667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24974255110085795927220889 18730691332564346945415667)
      ·
        refine ⟨28096036998846520418123501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18730691332564346945415667 28096036998846520418123501)
        ·
          refine ⟨10536013874567445156796313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28096036998846520418123501 10536013874567445156796313)
          ·
            refine ⟨7902010405925583867597235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10536013874567445156796313 7902010405925583867597235)
            ·
              refine ⟨11853015608888375801395853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7902010405925583867597235 11853015608888375801395853)
              ·
                refine ⟨4444880853333140925523445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11853015608888375801395853 4444880853333140925523445)
                ·
                  refine ⟨416707579999981961767823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4444880853333140925523445 416707579999981961767823)
                  ·
                    rfl

theorem cell20_912977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_912977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912977 prefixEnd_912977 := by exact prefixLift 912977
  have htrace : WordTrace (prefixWord ++ tailWord_912977) baseStart_912977 baseEnd_912977 := by
    simpa [prefixWord, tailWord_912977, baseEnd_912977] using wordTrace_append hprefix tailTrace_912977
  have hstable : (prefixWord ++ tailWord_912977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912977).length < 2 ^ (prefixWord ++ tailWord_912977).sum := by decide
  have hdescent : baseEnd_912977 < baseStart_912977 := by decide
  rcases family_descends (prefixWord ++ tailWord_912977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913008 : List Nat := [2, 1, 1, 1, 6, 1, 2, 6]
def baseStart_913008 : Nat := 118140960795 + 913008 * 2 ^ 59
def prefixEnd_913008 : Nat := 4983230072969 + 3 ^ 40 * 913008 * 2
def baseEnd_913008 : Nat := 138907243081561210578121

theorem tailTrace_913008 : CollatzResearch.WordTrace tailWord_913008 prefixEnd_913008 138907243081561210578121 := by
  unfold tailWord_913008
  simp only [CollatzResearch.WordTrace]
  refine ⟨16650068738167710098669839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22200091650890280131559785 16650068738167710098669839)
  ·
    refine ⟨24975103107251565148004759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16650068738167710098669839 24975103107251565148004759)
    ·
      refine ⟨37462654660877347722007139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24975103107251565148004759 37462654660877347722007139)
      ·
        refine ⟨56193981991316021583010709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37462654660877347722007139 56193981991316021583010709)
        ·
          refine ⟨2634092905842938511703627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56193981991316021583010709 2634092905842938511703627)
          ·
            refine ⟨3951139358764407767555441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634092905842938511703627 3951139358764407767555441)
            ·
              refine ⟨2963354519073305825666581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3951139358764407767555441 2963354519073305825666581)
              ·
                refine ⟨138907243081561210578121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2963354519073305825666581 138907243081561210578121)
                ·
                  rfl

theorem cell20_913008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_913008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913008 prefixEnd_913008 := by exact prefixLift 913008
  have htrace : WordTrace (prefixWord ++ tailWord_913008) baseStart_913008 baseEnd_913008 := by
    simpa [prefixWord, tailWord_913008, baseEnd_913008] using wordTrace_append hprefix tailTrace_913008
  have hstable : (prefixWord ++ tailWord_913008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913008).length < 2 ^ (prefixWord ++ tailWord_913008).sum := by decide
  have hdescent : baseEnd_913008 < baseStart_913008 := by decide
  rcases family_descends (prefixWord ++ tailWord_913008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913042 : List Nat := [3, 2, 3, 1, 3, 2, 1, 5]
def baseStart_913042 : Nat := 118140960795 + 913042 * 2 ^ 59
def prefixEnd_913042 : Nat := 4983230072969 + 3 ^ 40 * 913042 * 2
def baseEnd_913042 : Nat := 138912415923710208200297

theorem tailTrace_913042 : CollatzResearch.WordTrace tailWord_913042 prefixEnd_913042 138912415923710208200297 := by
  unfold tailWord_913042
  simp only [CollatzResearch.WordTrace]
  refine ⟨8325344389553061001019345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22200918372141496002718253 8325344389553061001019345)
  ·
    refine ⟨6244008292164795750764509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8325344389553061001019345 6244008292164795750764509)
    ·
      refine ⟨2341503109561798406536691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6244008292164795750764509 2341503109561798406536691)
      ·
        refine ⟨3512254664342697609805037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2341503109561798406536691 3512254664342697609805037)
        ·
          refine ⟨1317095499128511603676889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3512254664342697609805037 1317095499128511603676889)
          ·
            refine ⟨987821624346383702757667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1317095499128511603676889 987821624346383702757667)
            ·
              refine ⟨1481732436519575554136501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987821624346383702757667 1481732436519575554136501)
              ·
                refine ⟨138912415923710208200297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1481732436519575554136501 138912415923710208200297)
                ·
                  rfl

theorem cell20_913042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_913042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913042 prefixEnd_913042 := by exact prefixLift 913042
  have htrace : WordTrace (prefixWord ++ tailWord_913042) baseStart_913042 baseEnd_913042 := by
    simpa [prefixWord, tailWord_913042, baseEnd_913042] using wordTrace_append hprefix tailTrace_913042
  have hstable : (prefixWord ++ tailWord_913042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913042).length < 2 ^ (prefixWord ++ tailWord_913042).sum := by decide
  have hdescent : baseEnd_913042 < baseStart_913042 := by decide
  rcases family_descends (prefixWord ++ tailWord_913042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913053 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 7]
def baseStart_913053 : Nat := 118140960795 + 913053 * 2 ^ 59
def prefixEnd_913053 : Nat := 4983230072969 + 3 ^ 40 * 913053 * 2
def baseEnd_913053 : Nat := 416742268470863475234179

theorem tailTrace_913053 : CollatzResearch.WordTrace tailWord_913053 prefixEnd_913053 416742268470863475234179 := by
  unfold tailWord_913053
  simp only [CollatzResearch.WordTrace]
  refine ⟨33301778761172392882727813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22201185840781595255151875 33301778761172392882727813)
  ·
    refine ⟨6244083517719823665511465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33301778761172392882727813 6244083517719823665511465)
    ·
      refine ⟨4683062638289867749133599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6244083517719823665511465 4683062638289867749133599)
      ·
        refine ⟨7024593957434801623700399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4683062638289867749133599 7024593957434801623700399)
        ·
          refine ⟨10536890936152202435550599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7024593957434801623700399 10536890936152202435550599)
          ·
            refine ⟨15805336404228303653325899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10536890936152202435550599 15805336404228303653325899)
            ·
              refine ⟨23708004606342455479988849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15805336404228303653325899 23708004606342455479988849)
              ·
                refine ⟨17781003454756841609991637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23708004606342455479988849 17781003454756841609991637)
                ·
                  refine ⟨416742268470863475234179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17781003454756841609991637 416742268470863475234179)
                  ·
                    rfl

theorem cell20_913053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_913053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913053 prefixEnd_913053 := by exact prefixLift 913053
  have htrace : WordTrace (prefixWord ++ tailWord_913053) baseStart_913053 baseEnd_913053 := by
    simpa [prefixWord, tailWord_913053, baseEnd_913053] using wordTrace_append hprefix tailTrace_913053
  have hstable : (prefixWord ++ tailWord_913053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913053).length < 2 ^ (prefixWord ++ tailWord_913053).sum := by decide
  have hdescent : baseEnd_913053 < baseStart_913053 := by decide
  rcases family_descends (prefixWord ++ tailWord_913053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913084 : List Nat := [2, 2, 2, 3, 1, 3, 7]
def baseStart_913084 : Nat := 118140960795 + 913084 * 2 ^ 59
def prefixEnd_913084 : Nat := 4983230072969 + 3 ^ 40 * 913084 * 2
def baseEnd_913084 : Nat := 46306268635062793911191

theorem tailTrace_913084 : CollatzResearch.WordTrace tailWord_913084 prefixEnd_913084 46306268635062793911191 := by
  unfold tailWord_913084
  simp only [CollatzResearch.WordTrace]
  refine ⟨16651454712030042588553153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22201939616040056784737537 16651454712030042588553153)
  ·
    refine ⟨12488591034022531941414865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16651454712030042588553153 12488591034022531941414865)
    ·
      refine ⟨9366443275516898956061149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12488591034022531941414865 9366443275516898956061149)
      ·
        refine ⟨3512416228318837108522931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9366443275516898956061149 3512416228318837108522931)
        ·
          refine ⟨5268624342478255662784397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3512416228318837108522931 5268624342478255662784397)
          ·
            refine ⟨1975734128429345873544149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5268624342478255662784397 1975734128429345873544149)
            ·
              refine ⟨46306268635062793911191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1975734128429345873544149 46306268635062793911191)
              ·
                rfl

theorem cell20_913084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 7].length) (baseStart_913084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913084 prefixEnd_913084 := by exact prefixLift 913084
  have htrace : WordTrace (prefixWord ++ tailWord_913084) baseStart_913084 baseEnd_913084 := by
    simpa [prefixWord, tailWord_913084, baseEnd_913084] using wordTrace_append hprefix tailTrace_913084
  have hstable : (prefixWord ++ tailWord_913084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913084).length < 2 ^ (prefixWord ++ tailWord_913084).sum := by decide
  have hdescent : baseEnd_913084 < baseStart_913084 := by decide
  rcases family_descends (prefixWord ++ tailWord_913084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913132 : List Nat := [2, 2, 1, 1, 2, 2, 5, 3, 2]
def baseStart_913132 : Nat := 118140960795 + 913132 * 2 ^ 59
def prefixEnd_913132 : Nat := 4983230072969 + 3 ^ 40 * 913132 * 2
def baseEnd_913132 : Nat := 416778326223490311600523

theorem tailTrace_913132 : CollatzResearch.WordTrace tailWord_913132 prefixEnd_913132 416778326223490311600523 := by
  unfold tailWord_913132
  simp only [CollatzResearch.WordTrace]
  refine ⟨16652330063943094687426825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22203106751924126249902433 16652330063943094687426825)
  ·
    refine ⟨12489247547957321015570119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16652330063943094687426825 12489247547957321015570119)
    ·
      refine ⟨18733871321935981523355179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12489247547957321015570119 18733871321935981523355179)
      ·
        refine ⟨28100806982903972285032769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18733871321935981523355179 28100806982903972285032769)
        ·
          refine ⟨21075605237177979213774577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28100806982903972285032769 21075605237177979213774577)
          ·
            refine ⟨15806703927883484410330933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21075605237177979213774577 15806703927883484410330933)
            ·
              refine ⟨1481878493239076663468525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15806703927883484410330933 1481878493239076663468525)
              ·
                refine ⟨555704434964653748800697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1481878493239076663468525 555704434964653748800697)
                ·
                  refine ⟨416778326223490311600523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555704434964653748800697 416778326223490311600523)
                  ·
                    rfl

theorem cell20_913132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_913132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913132 prefixEnd_913132 := by exact prefixLift 913132
  have htrace : WordTrace (prefixWord ++ tailWord_913132) baseStart_913132 baseEnd_913132 := by
    simpa [prefixWord, tailWord_913132, baseEnd_913132] using wordTrace_append hprefix tailTrace_913132
  have hstable : (prefixWord ++ tailWord_913132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913132).length < 2 ^ (prefixWord ++ tailWord_913132).sum := by decide
  have hdescent : baseEnd_913132 < baseStart_913132 := by decide
  rcases family_descends (prefixWord ++ tailWord_913132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913143 : List Nat := [1, 1, 3, 1, 1, 1, 12]
def baseStart_913143 : Nat := 118140960795 + 913143 * 2 ^ 59
def prefixEnd_913143 : Nat := 4983230072969 + 3 ^ 40 * 913143 * 2
def baseEnd_913143 : Nat := 46309260769247018025979

theorem tailTrace_913143 : CollatzResearch.WordTrace tailWord_913143 prefixEnd_913143 46309260769247018025979 := by
  unfold tailWord_913143
  simp only [CollatzResearch.WordTrace]
  refine ⟨33305061330846338253504083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22203374220564225502336055 33305061330846338253504083)
  ·
    refine ⟨49957591996269507380256125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33305061330846338253504083 49957591996269507380256125)
    ·
      refine ⟨18734096998601065267596047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49957591996269507380256125 18734096998601065267596047)
      ·
        refine ⟨28101145497901597901394071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18734096998601065267596047 28101145497901597901394071)
        ·
          refine ⟨42151718246852396852091107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28101145497901597901394071 42151718246852396852091107)
          ·
            refine ⟨63227577370278595278136661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42151718246852396852091107 63227577370278595278136661)
            ·
              refine ⟨46309260769247018025979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 63227577370278595278136661 46309260769247018025979)
              ·
                rfl

theorem cell20_913143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 12].length) (baseStart_913143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913143 prefixEnd_913143 := by exact prefixLift 913143
  have htrace : WordTrace (prefixWord ++ tailWord_913143) baseStart_913143 baseEnd_913143 := by
    simpa [prefixWord, tailWord_913143, baseEnd_913143] using wordTrace_append hprefix tailTrace_913143
  have hstable : (prefixWord ++ tailWord_913143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913143).length < 2 ^ (prefixWord ++ tailWord_913143).sum := by decide
  have hdescent : baseEnd_913143 < baseStart_913143 := by decide
  rcases family_descends (prefixWord ++ tailWord_913143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913153 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 4]
def baseStart_913153 : Nat := 118140960795 + 913153 * 2 ^ 59
def prefixEnd_913153 : Nat := 4983230072969 + 3 ^ 40 * 913153 * 2
def baseEnd_913153 : Nat := 416787911195707571900437

theorem tailTrace_913153 : CollatzResearch.WordTrace tailWord_913153 prefixEnd_913153 416787911195707571900437 := by
  unfold tailWord_913153
  simp only [CollatzResearch.WordTrace]
  refine ⟨33305426060810109961368113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22203617373873406640912075 33305426060810109961368113)
  ·
    refine ⟨24979069545607582471026085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33305426060810109961368113 24979069545607582471026085)
    ·
      refine ⟨4683575539801421713317391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24979069545607582471026085 4683575539801421713317391)
      ·
        refine ⟨7025363309702132569976087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4683575539801421713317391 7025363309702132569976087)
        ·
          refine ⟨10538044964553198854964131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7025363309702132569976087 10538044964553198854964131)
          ·
            refine ⟨15807067446829798282446197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10538044964553198854964131 15807067446829798282446197)
            ·
              refine ⟨1481912573140293588979331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15807067446829798282446197 1481912573140293588979331)
              ·
                refine ⟨2222868859710440383468997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481912573140293588979331 2222868859710440383468997)
                ·
                  refine ⟨416787911195707571900437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2222868859710440383468997 416787911195707571900437)
                  ·
                    rfl

theorem cell20_913153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_913153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913153 prefixEnd_913153 := by exact prefixLift 913153
  have htrace : WordTrace (prefixWord ++ tailWord_913153) baseStart_913153 baseEnd_913153 := by
    simpa [prefixWord, tailWord_913153, baseEnd_913153] using wordTrace_append hprefix tailTrace_913153
  have hstable : (prefixWord ++ tailWord_913153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913153).length < 2 ^ (prefixWord ++ tailWord_913153).sum := by decide
  have hdescent : baseEnd_913153 < baseStart_913153 := by decide
  rcases family_descends (prefixWord ++ tailWord_913153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913159 : List Nat := [1, 1, 4, 4, 3, 1, 2, 1, 3]
def baseStart_913159 : Nat := 118140960795 + 913159 * 2 ^ 59
def prefixEnd_913159 : Nat := 4983230072969 + 3 ^ 40 * 913159 * 2
def baseEnd_913159 : Nat := 416790649759198217700413

theorem tailTrace_913159 : CollatzResearch.WordTrace tailWord_913159 prefixEnd_913159 416790649759198217700413 := by
  unfold tailWord_913159
  simp only [CollatzResearch.WordTrace]
  refine ⟨33305644898788372986086531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22203763265858915324057687 33305644898788372986086531)
  ·
    refine ⟨49958467348182559479129797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33305644898788372986086531 49958467348182559479129797)
    ·
      refine ⟨9367212627784229902336837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49958467348182559479129797 9367212627784229902336837)
      ·
        refine ⟨1756352367709543106688157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9367212627784229902336837 1756352367709543106688157)
        ·
          refine ⟨658632137891078665008059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1756352367709543106688157 658632137891078665008059)
          ·
            refine ⟨987948206836617997512089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658632137891078665008059 987948206836617997512089)
            ·
              refine ⟨740961155127463498134067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 987948206836617997512089 740961155127463498134067)
              ·
                refine ⟨1111441732691195247201101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740961155127463498134067 1111441732691195247201101)
                ·
                  refine ⟨416790649759198217700413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111441732691195247201101 416790649759198217700413)
                  ·
                    rfl

theorem cell20_913159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 3].length) (baseStart_913159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913159 prefixEnd_913159 := by exact prefixLift 913159
  have htrace : WordTrace (prefixWord ++ tailWord_913159) baseStart_913159 baseEnd_913159 := by
    simpa [prefixWord, tailWord_913159, baseEnd_913159] using wordTrace_append hprefix tailTrace_913159
  have hstable : (prefixWord ++ tailWord_913159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913159).length < 2 ^ (prefixWord ++ tailWord_913159).sum := by decide
  have hdescent : baseEnd_913159 < baseStart_913159 := by decide
  rcases family_descends (prefixWord ++ tailWord_913159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913160 : List Nat := [2, 1, 3, 2, 2, 1, 4, 5]
def baseStart_913160 : Nat := 118140960795 + 913160 * 2 ^ 59
def prefixEnd_913160 : Nat := 4983230072969 + 3 ^ 40 * 913160 * 2
def baseEnd_913160 : Nat := 138930368728815552889025

theorem tailTrace_913160 : CollatzResearch.WordTrace tailWord_913160 prefixEnd_913160 138930368728815552889025 := by
  unfold tailWord_913160
  simp only [CollatzResearch.WordTrace]
  refine ⟨16652840685892375078436467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22203787581189833437915289 16652840685892375078436467)
  ·
    refine ⟨24979261028838562617654701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16652840685892375078436467 24979261028838562617654701)
    ·
      refine ⟨9367222885814460981620513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24979261028838562617654701 9367222885814460981620513)
      ·
        refine ⟨7025417164360845736215385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9367222885814460981620513 7025417164360845736215385)
        ·
          refine ⟨5269062873270634302161539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7025417164360845736215385 5269062873270634302161539)
          ·
            refine ⟨7903594309905951453242309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5269062873270634302161539 7903594309905951453242309)
            ·
              refine ⟨1481923933107365897482933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7903594309905951453242309 1481923933107365897482933)
              ·
                refine ⟨138930368728815552889025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1481923933107365897482933 138930368728815552889025)
                ·
                  rfl

theorem cell20_913160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_913160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913160 prefixEnd_913160 := by exact prefixLift 913160
  have htrace : WordTrace (prefixWord ++ tailWord_913160) baseStart_913160 baseEnd_913160 := by
    simpa [prefixWord, tailWord_913160, baseEnd_913160] using wordTrace_append hprefix tailTrace_913160
  have hstable : (prefixWord ++ tailWord_913160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913160).length < 2 ^ (prefixWord ++ tailWord_913160).sum := by decide
  have hdescent : baseEnd_913160 < baseStart_913160 := by decide
  rcases family_descends (prefixWord ++ tailWord_913160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913198 : List Nat := [4, 1, 3, 2, 10]
def baseStart_913198 : Nat := 118140960795 + 913198 * 2 ^ 59
def prefixEnd_913198 : Nat := 4983230072969 + 3 ^ 40 * 913198 * 2
def baseEnd_913198 : Nat := 5145783338541819943213

theorem tailTrace_913198 : CollatzResearch.WordTrace tailWord_913198 prefixEnd_913198 5145783338541819943213 := by
  unfold tailWord_913198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4163383418205885330844531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22204711563764721764504165 4163383418205885330844531)
  ·
    refine ⟨6245075127308827996266797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4163383418205885330844531 6245075127308827996266797)
    ·
      refine ⟨2341903172740810498600049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6245075127308827996266797 2341903172740810498600049)
      ·
        refine ⟨1756427379555607873950037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2341903172740810498600049 1756427379555607873950037)
        ·
          refine ⟨5145783338541819943213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1756427379555607873950037 5145783338541819943213)
          ·
            rfl

theorem cell20_913198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 10].length) (baseStart_913198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913198 prefixEnd_913198 := by exact prefixLift 913198
  have htrace : WordTrace (prefixWord ++ tailWord_913198) baseStart_913198 baseEnd_913198 := by
    simpa [prefixWord, tailWord_913198, baseEnd_913198] using wordTrace_append hprefix tailTrace_913198
  have hstable : (prefixWord ++ tailWord_913198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913198).length < 2 ^ (prefixWord ++ tailWord_913198).sum := by decide
  have hdescent : baseEnd_913198 < baseStart_913198 := by decide
  rcases family_descends (prefixWord ++ tailWord_913198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913204 : List Nat := [2, 5, 1, 1, 2, 1, 4, 2, 2]
def baseStart_913204 : Nat := 118140960795 + 913204 * 2 ^ 59
def prefixEnd_913204 : Nat := 4983230072969 + 3 ^ 40 * 913204 * 2
def baseEnd_913204 : Nat := 416811188985378061200229

theorem tailTrace_913204 : CollatzResearch.WordTrace tailWord_913204 prefixEnd_913204 416811188985378061200229 := by
  unfold tailWord_913204
  simp only [CollatzResearch.WordTrace]
  refine ⟨16653643091812672835737333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22204857455750230447649777 16653643091812672835737333)
  ·
    refine ⟨1561279039857438078350375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16653643091812672835737333 1561279039857438078350375)
    ·
      refine ⟨2341918559786157117525563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1561279039857438078350375 2341918559786157117525563)
      ·
        refine ⟨3512877839679235676288345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2341918559786157117525563 3512877839679235676288345)
        ·
          refine ⟨2634658379759426757216259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3512877839679235676288345 2634658379759426757216259)
          ·
            refine ⟨3951987569639140135824389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634658379759426757216259 3951987569639140135824389)
            ·
              refine ⟨740997669307338775467073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3951987569639140135824389 740997669307338775467073)
              ·
                refine ⟨555748251980504081600305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740997669307338775467073 555748251980504081600305)
                ·
                  refine ⟨416811188985378061200229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555748251980504081600305 416811188985378061200229)
                  ·
                    rfl

theorem cell20_913204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_913204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913204 prefixEnd_913204 := by exact prefixLift 913204
  have htrace : WordTrace (prefixWord ++ tailWord_913204) baseStart_913204 baseEnd_913204 := by
    simpa [prefixWord, tailWord_913204, baseEnd_913204] using wordTrace_append hprefix tailTrace_913204
  have hstable : (prefixWord ++ tailWord_913204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913204).length < 2 ^ (prefixWord ++ tailWord_913204).sum := by decide
  have hdescent : baseEnd_913204 < baseStart_913204 := by decide
  rcases family_descends (prefixWord ++ tailWord_913204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913208 : List Nat := [2, 1, 2, 1, 3, 4, 1, 4, 2]
def baseStart_913208 : Nat := 118140960795 + 913208 * 2 ^ 59
def prefixEnd_913208 : Nat := 4983230072969 + 3 ^ 40 * 913208 * 2
def baseEnd_913208 : Nat := 416813014694371825066879

theorem tailTrace_913208 : CollatzResearch.WordTrace tailWord_913208 prefixEnd_913208 416813014694371825066879 := by
  unfold tailWord_913208
  simp only [CollatzResearch.WordTrace]
  refine ⟨16653716037805427177310139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22204954717073902903080185 16653716037805427177310139)
  ·
    refine ⟨24980574056708140765965209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16653716037805427177310139 24980574056708140765965209)
    ·
      refine ⟨18735430542531105574473907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24980574056708140765965209 18735430542531105574473907)
      ·
        refine ⟨28103145813796658361710861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18735430542531105574473907 28103145813796658361710861)
        ·
          refine ⟨10538679680173746885641573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28103145813796658361710861 10538679680173746885641573)
          ·
            refine ⟨1976002440032577541057795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10538679680173746885641573 1976002440032577541057795)
            ·
              refine ⟨2964003660048866311586693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976002440032577541057795 2964003660048866311586693)
              ·
                refine ⟨555750686259162433422505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2964003660048866311586693 555750686259162433422505)
                ·
                  refine ⟨416813014694371825066879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555750686259162433422505 416813014694371825066879)
                  ·
                    rfl

theorem cell20_913208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 2].length) (baseStart_913208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913208 prefixEnd_913208 := by exact prefixLift 913208
  have htrace : WordTrace (prefixWord ++ tailWord_913208) baseStart_913208 baseEnd_913208 := by
    simpa [prefixWord, tailWord_913208, baseEnd_913208] using wordTrace_append hprefix tailTrace_913208
  have hstable : (prefixWord ++ tailWord_913208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913208).length < 2 ^ (prefixWord ++ tailWord_913208).sum := by decide
  have hdescent : baseEnd_913208 < baseStart_913208 := by decide
  rcases family_descends (prefixWord ++ tailWord_913208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913215 : List Nat := [1, 1, 2, 2, 6, 2, 1, 5]
def baseStart_913215 : Nat := 118140960795 + 913215 * 2 ^ 59
def prefixEnd_913215 : Nat := 4983230072969 + 3 ^ 40 * 913215 * 2
def baseEnd_913215 : Nat := 138938736561703637277839

theorem tailTrace_913215 : CollatzResearch.WordTrace tailWord_913215 prefixEnd_913215 138938736561703637277839 := by
  unfold tailWord_913215
  simp only [CollatzResearch.WordTrace]
  refine ⟨33307687386585494550125099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22205124924390329700083399 33307687386585494550125099)
  ·
    refine ⟨49961531079878241825187649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33307687386585494550125099 49961531079878241825187649)
    ·
      refine ⟨37471148309908681368890737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49961531079878241825187649 37471148309908681368890737)
      ·
        refine ⟨28103361232431511026668053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37471148309908681368890737 28103361232431511026668053)
        ·
          refine ⟨1317345057770227079375065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28103361232431511026668053 1317345057770227079375065)
          ·
            refine ⟨988008793327670309531299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1317345057770227079375065 988008793327670309531299)
            ·
              refine ⟨1482013189991505464296949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 988008793327670309531299 1482013189991505464296949)
              ·
                refine ⟨138938736561703637277839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1482013189991505464296949 138938736561703637277839)
                ·
                  rfl

theorem cell20_913215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 5].length) (baseStart_913215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913215 prefixEnd_913215 := by exact prefixLift 913215
  have htrace : WordTrace (prefixWord ++ tailWord_913215) baseStart_913215 baseEnd_913215 := by
    simpa [prefixWord, tailWord_913215, baseEnd_913215] using wordTrace_append hprefix tailTrace_913215
  have hstable : (prefixWord ++ tailWord_913215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913215).length < 2 ^ (prefixWord ++ tailWord_913215).sum := by decide
  have hdescent : baseEnd_913215 < baseStart_913215 := by decide
  rcases family_descends (prefixWord ++ tailWord_913215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913260 : List Nat := [2, 2, 1, 1, 4, 2, 3, 2, 3]
def baseStart_913260 : Nat := 118140960795 + 913260 * 2 ^ 59
def prefixEnd_913260 : Nat := 4983230072969 + 3 ^ 40 * 913260 * 2
def baseEnd_913260 : Nat := 416836748911290755333333

theorem tailTrace_913260 : CollatzResearch.WordTrace tailWord_913260 prefixEnd_913260 416836748911290755333333 := by
  unfold tailWord_913260
  simp only [CollatzResearch.WordTrace]
  refine ⟨16654664335711233617756617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22206219114281644823675489 16654664335711233617756617)
  ·
    refine ⟨12490998251783425213317463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16654664335711233617756617 12490998251783425213317463)
    ·
      refine ⟨18736497377675137819976195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12490998251783425213317463 18736497377675137819976195)
      ·
        refine ⟨28104746066512706729964293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18736497377675137819976195 28104746066512706729964293)
        ·
          refine ⟨5269639887471132511868305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28104746066512706729964293 5269639887471132511868305)
          ·
            refine ⟨3952229915603349383901229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5269639887471132511868305 3952229915603349383901229)
            ·
              refine ⟨1482086218351256018962961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3952229915603349383901229 1482086218351256018962961)
              ·
                refine ⟨1111564663763442014222221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1482086218351256018962961 1111564663763442014222221)
                ·
                  refine ⟨416836748911290755333333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111564663763442014222221 416836748911290755333333)
                  ·
                    rfl

theorem cell20_913260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_913260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913260 prefixEnd_913260 := by exact prefixLift 913260
  have htrace : WordTrace (prefixWord ++ tailWord_913260) baseStart_913260 baseEnd_913260 := by
    simpa [prefixWord, tailWord_913260, baseEnd_913260] using wordTrace_append hprefix tailTrace_913260
  have hstable : (prefixWord ++ tailWord_913260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913260).length < 2 ^ (prefixWord ++ tailWord_913260).sum := by decide
  have hdescent : baseEnd_913260 < baseStart_913260 := by decide
  rcases family_descends (prefixWord ++ tailWord_913260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913298 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_913298 : Nat := 118140960795 + 913298 * 2 ^ 59
def prefixEnd_913298 : Nat := 4983230072969 + 3 ^ 40 * 913298 * 2
def baseEnd_913298 : Nat := 416854093146731512066511

theorem tailTrace_913298 : CollatzResearch.WordTrace tailWord_913298 prefixEnd_913298 416854093146731512066511 := by
  unfold tailWord_913298
  simp only [CollatzResearch.WordTrace]
  refine ⟨8327678661321199931349137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22207143096856533150264365 8327678661321199931349137)
  ·
    refine ⟨6245758995990899948511853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8327678661321199931349137 6245758995990899948511853)
    ·
      refine ⟨2342159623496587480691945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6245758995990899948511853 2342159623496587480691945)
      ·
        refine ⟨1756619717622440610518959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2342159623496587480691945 1756619717622440610518959)
        ·
          refine ⟨2634929576433660915778439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1756619717622440610518959 2634929576433660915778439)
          ·
            refine ⟨3952394364650491373667659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634929576433660915778439 3952394364650491373667659)
            ·
              refine ⟨5928591546975737060501489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3952394364650491373667659 5928591546975737060501489)
              ·
                refine ⟨4446443660231802795376117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5928591546975737060501489 4446443660231802795376117)
                ·
                  refine ⟨416854093146731512066511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4446443660231802795376117 416854093146731512066511)
                  ·
                    rfl

theorem cell20_913298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_913298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913298 prefixEnd_913298 := by exact prefixLift 913298
  have htrace : WordTrace (prefixWord ++ tailWord_913298) baseStart_913298 baseEnd_913298 := by
    simpa [prefixWord, tailWord_913298, baseEnd_913298] using wordTrace_append hprefix tailTrace_913298
  have hstable : (prefixWord ++ tailWord_913298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913298).length < 2 ^ (prefixWord ++ tailWord_913298).sum := by decide
  have hdescent : baseEnd_913298 < baseStart_913298 := by decide
  rcases family_descends (prefixWord ++ tailWord_913298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913332 : List Nat := [2, 5, 2, 1, 2, 1, 1, 3, 3]
def baseStart_913332 : Nat := 118140960795 + 913332 * 2 ^ 59
def prefixEnd_913332 : Nat := 4983230072969 + 3 ^ 40 * 913332 * 2
def baseEnd_913332 : Nat := 416869611673178504933039

theorem tailTrace_913332 : CollatzResearch.WordTrace tailWord_913332 prefixEnd_913332 416869611673178504933039 := by
  unfold tailWord_913332
  simp only [CollatzResearch.WordTrace]
  refine ⟨16655977363580811766067125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22207969818107749021422833 16655977363580811766067125)
  ·
    refine ⟨1561497877835701103068793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16655977363580811766067125 1561497877835701103068793)
    ·
      refine ⟨1171123408376775827301595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1561497877835701103068793 1171123408376775827301595)
      ·
        refine ⟨1756685112565163740952393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1171123408376775827301595 1756685112565163740952393)
        ·
          refine ⟨1317513834423872805714295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1756685112565163740952393 1317513834423872805714295)
          ·
            refine ⟨1976270751635809208571443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317513834423872805714295 1976270751635809208571443)
            ·
              refine ⟨2964406127453713812857165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976270751635809208571443 2964406127453713812857165)
              ·
                refine ⟨1111652297795142679821437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2964406127453713812857165 1111652297795142679821437)
                ·
                  refine ⟨416869611673178504933039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111652297795142679821437 416869611673178504933039)
                  ·
                    rfl

theorem cell20_913332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_913332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913332 prefixEnd_913332 := by exact prefixLift 913332
  have htrace : WordTrace (prefixWord ++ tailWord_913332) baseStart_913332 baseEnd_913332 := by
    simpa [prefixWord, tailWord_913332, baseEnd_913332] using wordTrace_append hprefix tailTrace_913332
  have hstable : (prefixWord ++ tailWord_913332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913332).length < 2 ^ (prefixWord ++ tailWord_913332).sum := by decide
  have hdescent : baseEnd_913332 < baseStart_913332 := by decide
  rcases family_descends (prefixWord ++ tailWord_913332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913373 : List Nat := [1, 4, 3, 1, 4, 1, 2, 2, 2]
def baseStart_913373 : Nat := 118140960795 + 913373 * 2 ^ 59
def prefixEnd_913373 : Nat := 4983230072969 + 3 ^ 40 * 913373 * 2
def baseEnd_913373 : Nat := 416888325190364584566205

theorem tailTrace_913373 : CollatzResearch.WordTrace tailWord_913373 prefixEnd_913373 416888325190364584566205 := by
  unfold tailWord_913373
  simp only [CollatzResearch.WordTrace]
  refine ⟨33313450120013087534376773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22208966746675391689584515 33313450120013087534376773)
  ·
    refine ⟨6246271897502453912695645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33313450120013087534376773 6246271897502453912695645)
    ·
      refine ⟨2342351961563420217260867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6246271897502453912695645 2342351961563420217260867)
      ·
        refine ⟨3513527942345130325891301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2342351961563420217260867 3513527942345130325891301)
        ·
          refine ⟨658786489189711936104619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3513527942345130325891301 658786489189711936104619)
          ·
            refine ⟨988179733784567904156929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658786489189711936104619 988179733784567904156929)
            ·
              refine ⟨741134800338425928117697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988179733784567904156929 741134800338425928117697)
              ·
                refine ⟨555851100253819446088273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741134800338425928117697 555851100253819446088273)
                ·
                  refine ⟨416888325190364584566205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555851100253819446088273 416888325190364584566205)
                  ·
                    rfl

theorem cell20_913373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_913373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913373 prefixEnd_913373 := by exact prefixLift 913373
  have htrace : WordTrace (prefixWord ++ tailWord_913373) baseStart_913373 baseEnd_913373 := by
    simpa [prefixWord, tailWord_913373, baseEnd_913373] using wordTrace_append hprefix tailTrace_913373
  have hstable : (prefixWord ++ tailWord_913373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913373).length < 2 ^ (prefixWord ++ tailWord_913373).sum := by decide
  have hdescent : baseEnd_913373 < baseStart_913373 := by decide
  rcases family_descends (prefixWord ++ tailWord_913373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913398 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_913398 : Nat := 118140960795 + 913398 * 2 ^ 59
def prefixEnd_913398 : Nat := 4983230072969 + 3 ^ 40 * 913398 * 2
def baseEnd_913398 : Nat := 416899735871575608732769

theorem tailTrace_913398 : CollatzResearch.WordTrace tailWord_913398 prefixEnd_913398 416899735871575608732769 := by
  unfold tailWord_913398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2082147621557657300252303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22209574629948344536024565 2082147621557657300252303)
  ·
    refine ⟨3123221432336485950378455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2082147621557657300252303 3123221432336485950378455)
    ·
      refine ⟨4684832148504728925567683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3123221432336485950378455 4684832148504728925567683)
      ·
        refine ⟨7027248222757093388351525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4684832148504728925567683 7027248222757093388351525)
        ·
          refine ⟨1317609041766955010315911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7027248222757093388351525 1317609041766955010315911)
          ·
            refine ⟨1976413562650432515473867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317609041766955010315911 1976413562650432515473867)
            ·
              refine ⟨2964620343975648773210801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976413562650432515473867 2964620343975648773210801)
              ·
                refine ⟨2223465257981736579908101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2964620343975648773210801 2223465257981736579908101)
                ·
                  refine ⟨416899735871575608732769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2223465257981736579908101 416899735871575608732769)
                  ·
                    rfl

theorem cell20_913398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_913398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913398 prefixEnd_913398 := by exact prefixLift 913398
  have htrace : WordTrace (prefixWord ++ tailWord_913398) baseStart_913398 baseEnd_913398 := by
    simpa [prefixWord, tailWord_913398, baseEnd_913398] using wordTrace_append hprefix tailTrace_913398
  have hstable : (prefixWord ++ tailWord_913398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913398).length < 2 ^ (prefixWord ++ tailWord_913398).sum := by decide
  have hdescent : baseEnd_913398 < baseStart_913398 := by decide
  rcases family_descends (prefixWord ++ tailWord_913398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913429 : List Nat := [1, 3, 2, 1, 5, 2, 1, 2, 3]
def baseStart_913429 : Nat := 118140960795 + 913429 * 2 ^ 59
def prefixEnd_913429 : Nat := 4983230072969 + 3 ^ 40 * 913429 * 2
def baseEnd_913429 : Nat := 416913885116277278699309

theorem tailTrace_913429 : CollatzResearch.WordTrace tailWord_913429 prefixEnd_913429 416913885116277278699309 := by
  unfold tailWord_913429
  simp only [CollatzResearch.WordTrace]
  refine ⟨33315492607810209098415341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22210328405206806065610227 33315492607810209098415341)
  ·
    refine ⟨12493309727928828411905753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33315492607810209098415341 12493309727928828411905753)
    ·
      refine ⟨9369982295946621308929315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12493309727928828411905753 9369982295946621308929315)
      ·
        refine ⟨14054973443919931963393973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9369982295946621308929315 14054973443919931963393973)
        ·
          refine ⟨1317653760367493621568185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14054973443919931963393973 1317653760367493621568185)
          ·
            refine ⟨988240320275620216176139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1317653760367493621568185 988240320275620216176139)
            ·
              refine ⟨1482360480413430324264209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 988240320275620216176139 1482360480413430324264209)
              ·
                refine ⟨1111770360310072743198157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1482360480413430324264209 1111770360310072743198157)
                ·
                  refine ⟨416913885116277278699309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111770360310072743198157 416913885116277278699309)
                  ·
                    rfl

theorem cell20_913429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_913429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913429 prefixEnd_913429 := by exact prefixLift 913429
  have htrace : WordTrace (prefixWord ++ tailWord_913429) baseStart_913429 baseEnd_913429 := by
    simpa [prefixWord, tailWord_913429, baseEnd_913429] using wordTrace_append hprefix tailTrace_913429
  have hstable : (prefixWord ++ tailWord_913429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913429).length < 2 ^ (prefixWord ++ tailWord_913429).sum := by decide
  have hdescent : baseEnd_913429 < baseStart_913429 := by decide
  rcases family_descends (prefixWord ++ tailWord_913429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913436 : List Nat := [2, 2, 3, 1, 3, 1, 2, 4, 2]
def baseStart_913436 : Nat := 118140960795 + 913436 * 2 ^ 59
def prefixEnd_913436 : Nat := 4983230072969 + 3 ^ 40 * 913436 * 2
def baseEnd_913436 : Nat := 416917080107016365465947

theorem tailTrace_913436 : CollatzResearch.WordTrace tailWord_913436 prefixEnd_913436 416917080107016365465947 := by
  unfold tailWord_913436
  simp only [CollatzResearch.WordTrace]
  refine ⟨16657873959392424646960081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22210498612523232862613441 16657873959392424646960081)
  ·
    refine ⟨12493405469544318485220061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16657873959392424646960081 12493405469544318485220061)
    ·
      refine ⟨4685027051079119431957523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12493405469544318485220061 4685027051079119431957523)
      ·
        refine ⟨7027540576618679147936285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4685027051079119431957523 7027540576618679147936285)
        ·
          refine ⟨2635327716232004680476107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7027540576618679147936285 2635327716232004680476107)
          ·
            refine ⟨3952991574348007020714161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2635327716232004680476107 3952991574348007020714161)
            ·
              refine ⟨2964743680761005265535621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3952991574348007020714161 2964743680761005265535621)
              ·
                refine ⟨555889440142688487287929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2964743680761005265535621 555889440142688487287929)
                ·
                  refine ⟨416917080107016365465947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555889440142688487287929 416917080107016365465947)
                  ·
                    rfl

theorem cell20_913436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_913436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913436 prefixEnd_913436 := by exact prefixLift 913436
  have htrace : WordTrace (prefixWord ++ tailWord_913436) baseStart_913436 baseEnd_913436 := by
    simpa [prefixWord, tailWord_913436, baseEnd_913436] using wordTrace_append hprefix tailTrace_913436
  have hstable : (prefixWord ++ tailWord_913436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913436).length < 2 ^ (prefixWord ++ tailWord_913436).sum := by decide
  have hdescent : baseEnd_913436 < baseStart_913436 := by decide
  rcases family_descends (prefixWord ++ tailWord_913436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913464 : List Nat := [2, 1, 2, 1, 6, 1, 1, 6]
def baseStart_913464 : Nat := 118140960795 + 913464 * 2 ^ 59
def prefixEnd_913464 : Nat := 4983230072969 + 3 ^ 40 * 913464 * 2
def baseEnd_913464 : Nat := 138976620023324237510833

theorem tailTrace_913464 : CollatzResearch.WordTrace tailWord_913464 prefixEnd_913464 138976620023324237510833 := by
  unfold tailWord_913464
  simp only [CollatzResearch.WordTrace]
  refine ⟨16658384581341705037969723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22211179441788940050626297 16658384581341705037969723)
  ·
    refine ⟨24987576872012557556954585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16658384581341705037969723 24987576872012557556954585)
    ·
      refine ⟨18740682654009418167715939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24987576872012557556954585 18740682654009418167715939)
      ·
        refine ⟨28111023981014127251573909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18740682654009418167715939 28111023981014127251573909)
        ·
          refine ⟨1317704249110037214917527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28111023981014127251573909 1317704249110037214917527)
          ·
            refine ⟨1976556373665055822376291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317704249110037214917527 1976556373665055822376291)
            ·
              refine ⟨2964834560497583733564437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976556373665055822376291 2964834560497583733564437)
              ·
                refine ⟨138976620023324237510833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2964834560497583733564437 138976620023324237510833)
                ·
                  rfl

theorem cell20_913464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_913464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913464 prefixEnd_913464 := by exact prefixLift 913464
  have htrace : WordTrace (prefixWord ++ tailWord_913464) baseStart_913464 baseEnd_913464 := by
    simpa [prefixWord, tailWord_913464, baseEnd_913464] using wordTrace_append hprefix tailTrace_913464
  have hstable : (prefixWord ++ tailWord_913464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913464).length < 2 ^ (prefixWord ++ tailWord_913464).sum := by decide
  have hdescent : baseEnd_913464 < baseStart_913464 := by decide
  rcases family_descends (prefixWord ++ tailWord_913464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913470 : List Nat := [4, 2, 1, 3, 2, 2, 1, 3, 2]
def baseStart_913470 : Nat := 118140960795 + 913470 * 2 ^ 59
def prefixEnd_913470 : Nat := 4983230072969 + 3 ^ 40 * 913470 * 2
def baseEnd_913470 : Nat := 416932598633463358332475

theorem tailTrace_913470 : CollatzResearch.WordTrace tailWord_913470 prefixEnd_913470 416932598633463358332475 := by
  unfold tailWord_913470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4164623500082709137582233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22211325333774448733771909 4164623500082709137582233)
  ·
    refine ⟨3123467625062031853186675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4164623500082709137582233 3123467625062031853186675)
    ·
      refine ⟨4685201437593047779780013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3123467625062031853186675 4685201437593047779780013)
      ·
        refine ⟨1756950539097392917417505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4685201437593047779780013 1756950539097392917417505)
        ·
          refine ⟨1317712904323044688063129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1756950539097392917417505 1317712904323044688063129)
          ·
            refine ⟨988284678242283516047347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1317712904323044688063129 988284678242283516047347)
            ·
              refine ⟨1482427017363425274071021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 988284678242283516047347 1482427017363425274071021)
              ·
                refine ⟨555910131511284477776633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1482427017363425274071021 555910131511284477776633)
                ·
                  refine ⟨416932598633463358332475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555910131511284477776633 416932598633463358332475)
                  ·
                    rfl

theorem cell20_913470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_913470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913470 prefixEnd_913470 := by exact prefixLift 913470
  have htrace : WordTrace (prefixWord ++ tailWord_913470) baseStart_913470 baseEnd_913470 := by
    simpa [prefixWord, tailWord_913470, baseEnd_913470] using wordTrace_append hprefix tailTrace_913470
  have hstable : (prefixWord ++ tailWord_913470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913470).length < 2 ^ (prefixWord ++ tailWord_913470).sum := by decide
  have hdescent : baseEnd_913470 < baseStart_913470 := by decide
  rcases family_descends (prefixWord ++ tailWord_913470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913495 : List Nat := [1, 1, 3, 2, 2, 1, 2, 6, 2]
def baseStart_913495 : Nat := 118140960795 + 913495 * 2 ^ 59
def prefixEnd_913495 : Nat := 4983230072969 + 3 ^ 40 * 913495 * 2
def baseEnd_913495 : Nat := 416944009314674382499039

theorem tailTrace_913495 : CollatzResearch.WordTrace tailWord_913495 prefixEnd_913495 416944009314674382499039 := by
  unfold tailWord_913495
  simp only [CollatzResearch.WordTrace]
  refine ⟨33317899825571102370317939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22211933217047401580211959 33317899825571102370317939)
  ·
    refine ⟨49976849738356653555476909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33317899825571102370317939 49976849738356653555476909)
    ·
      refine ⟨18741318651883745083303841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49976849738356653555476909 18741318651883745083303841)
      ·
        refine ⟨14055988988912808812477881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18741318651883745083303841 14055988988912808812477881)
        ·
          refine ⟨10541991741684606609358411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14055988988912808812477881 10541991741684606609358411)
          ·
            refine ⟨15812987612526909914037617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10541991741684606609358411 15812987612526909914037617)
            ·
              refine ⟨11859740709395182435528213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15812987612526909914037617 11859740709395182435528213)
              ·
                refine ⟨555925345752899176665385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11859740709395182435528213 555925345752899176665385)
                ·
                  refine ⟨416944009314674382499039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555925345752899176665385 416944009314674382499039)
                  ·
                    rfl

theorem cell20_913495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 2].length) (baseStart_913495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913495 prefixEnd_913495 := by exact prefixLift 913495
  have htrace : WordTrace (prefixWord ++ tailWord_913495) baseStart_913495 baseEnd_913495 := by
    simpa [prefixWord, tailWord_913495, baseEnd_913495] using wordTrace_append hprefix tailTrace_913495
  have hstable : (prefixWord ++ tailWord_913495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913495).length < 2 ^ (prefixWord ++ tailWord_913495).sum := by decide
  have hdescent : baseEnd_913495 < baseStart_913495 := by decide
  rcases family_descends (prefixWord ++ tailWord_913495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913598 : List Nat := [4, 2, 1, 1, 5, 1, 1, 2, 3]
def baseStart_913598 : Nat := 118140960795 + 913598 * 2 ^ 59
def prefixEnd_913598 : Nat := 4983230072969 + 3 ^ 40 * 913598 * 2
def baseEnd_913598 : Nat := 416991021321263802065285

theorem tailTrace_913598 : CollatzResearch.WordTrace tailWord_913598 prefixEnd_913598 416991021321263802065285 := by
  unfold tailWord_913598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4165207068024743870164681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22214437696131967307544965 4165207068024743870164681)
  ·
    refine ⟨3123905301018557902623511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4165207068024743870164681 3123905301018557902623511)
    ·
      refine ⟨4685857951527836853935267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3123905301018557902623511 4685857951527836853935267)
      ·
        refine ⟨7028786927291755280902901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4685857951527836853935267 7028786927291755280902901)
        ·
          refine ⟨658948774433602057584647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7028786927291755280902901 658948774433602057584647)
          ·
            refine ⟨988423161650403086376971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658948774433602057584647 988423161650403086376971)
            ·
              refine ⟨1482634742475604629565457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 988423161650403086376971 1482634742475604629565457)
              ·
                refine ⟨1111976056856703472174093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1482634742475604629565457 1111976056856703472174093)
                ·
                  refine ⟨416991021321263802065285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111976056856703472174093 416991021321263802065285)
                  ·
                    rfl

theorem cell20_913598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_913598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913598 prefixEnd_913598 := by exact prefixLift 913598
  have htrace : WordTrace (prefixWord ++ tailWord_913598) baseStart_913598 baseEnd_913598 := by
    simpa [prefixWord, tailWord_913598, baseEnd_913598] using wordTrace_append hprefix tailTrace_913598
  have hstable : (prefixWord ++ tailWord_913598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913598).length < 2 ^ (prefixWord ++ tailWord_913598).sum := by decide
  have hdescent : baseEnd_913598 < baseStart_913598 := by decide
  rcases family_descends (prefixWord ++ tailWord_913598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913644 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 7]
def baseStart_913644 : Nat := 118140960795 + 913644 * 2 ^ 59
def prefixEnd_913644 : Nat := 4983230072969 + 3 ^ 40 * 913644 * 2
def baseEnd_913644 : Nat := 417012016974692086531763

theorem tailTrace_913644 : CollatzResearch.WordTrace tailWord_913644 prefixEnd_913644 417012016974692086531763 := by
  unfold tailWord_913644
  simp only [CollatzResearch.WordTrace]
  refine ⟨16661667151015650408745993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22215556201354200544994657 16661667151015650408745993)
  ·
    refine ⟨12496250363261737806559495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16661667151015650408745993 12496250363261737806559495)
    ·
      refine ⟨18744375544892606709839243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12496250363261737806559495 18744375544892606709839243)
      ·
        refine ⟨28116563317338910064758865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18744375544892606709839243 28116563317338910064758865)
        ·
          refine ⟨21087422488004182548569149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28116563317338910064758865 21087422488004182548569149)
          ·
            refine ⟨7907783433001568455713431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21087422488004182548569149 7907783433001568455713431)
            ·
              refine ⟨11861675149502352683570147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7907783433001568455713431 11861675149502352683570147)
              ·
                refine ⟨17792512724253529025355221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11861675149502352683570147 17792512724253529025355221)
                ·
                  refine ⟨417012016974692086531763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17792512724253529025355221 417012016974692086531763)
                  ·
                    rfl

theorem cell20_913644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_913644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913644 prefixEnd_913644 := by exact prefixLift 913644
  have htrace : WordTrace (prefixWord ++ tailWord_913644) baseStart_913644 baseEnd_913644 := by
    simpa [prefixWord, tailWord_913644, baseEnd_913644] using wordTrace_append hprefix tailTrace_913644
  have hstable : (prefixWord ++ tailWord_913644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913644).length < 2 ^ (prefixWord ++ tailWord_913644).sum := by decide
  have hdescent : baseEnd_913644 < baseStart_913644 := by decide
  rcases family_descends (prefixWord ++ tailWord_913644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913671 : List Nat := [1, 1, 4, 5, 1, 1, 2, 5]
def baseStart_913671 : Nat := 118140960795 + 913671 * 2 ^ 59
def prefixEnd_913671 : Nat := 4983230072969 + 3 ^ 40 * 913671 * 2
def baseEnd_913671 : Nat := 139008113503466664210551

theorem tailTrace_913671 : CollatzResearch.WordTrace tailWord_913671 prefixEnd_913671 139008113503466664210551 := by
  unfold tailWord_913671
  simp only [CollatzResearch.WordTrace]
  refine ⟨33324319072933484428724867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22216212715288989619149911 33324319072933484428724867)
  ·
    refine ⟨49986478609400226643087301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33324319072933484428724867 49986478609400226643087301)
    ·
      refine ⟨9372464739262542495578869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49986478609400226643087301 9372464739262542495578869)
      ·
        refine ⟨878668569305863358960519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9372464739262542495578869 878668569305863358960519)
        ·
          refine ⟨1318002853958795038440779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878668569305863358960519 1318002853958795038440779)
          ·
            refine ⟨1977004280938192557661169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318002853958795038440779 1977004280938192557661169)
            ·
              refine ⟨1482753210703644418245877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1977004280938192557661169 1482753210703644418245877)
              ·
                refine ⟨139008113503466664210551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1482753210703644418245877 139008113503466664210551)
                ·
                  rfl

theorem cell20_913671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 5].length) (baseStart_913671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913671 prefixEnd_913671 := by exact prefixLift 913671
  have htrace : WordTrace (prefixWord ++ tailWord_913671) baseStart_913671 baseEnd_913671 := by
    simpa [prefixWord, tailWord_913671, baseEnd_913671] using wordTrace_append hprefix tailTrace_913671
  have hstable : (prefixWord ++ tailWord_913671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913671).length < 2 ^ (prefixWord ++ tailWord_913671).sum := by decide
  have hdescent : baseEnd_913671 < baseStart_913671 := by decide
  rcases family_descends (prefixWord ++ tailWord_913671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913675 : List Nat := [1, 1, 1, 1, 5, 2, 4, 5]
def baseStart_913675 : Nat := 118140960795 + 913675 * 2 ^ 59
def prefixEnd_913675 : Nat := 4983230072969 + 3 ^ 40 * 913675 * 2
def baseEnd_913675 : Nat := 139008722073131252166101

theorem tailTrace_913675 : CollatzResearch.WordTrace tailWord_913675 prefixEnd_913675 139008722073131252166101 := by
  unfold tailWord_913675
  simp only [CollatzResearch.WordTrace]
  refine ⟨33324464964918993111870479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22216309976612662074580319 33324464964918993111870479)
  ·
    refine ⟨49986697447378489667805719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33324464964918993111870479 49986697447378489667805719)
    ·
      refine ⟨74980046171067734501708579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49986697447378489667805719 74980046171067734501708579)
      ·
        refine ⟨112470069256601601752562869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74980046171067734501708579 112470069256601601752562869)
        ·
          refine ⟨10544068992806400164302769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112470069256601601752562869 10544068992806400164302769)
          ·
            refine ⟨7908051744604800123227077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10544068992806400164302769 7908051744604800123227077)
            ·
              refine ⟨1482759702113400023105077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7908051744604800123227077 1482759702113400023105077)
              ·
                refine ⟨139008722073131252166101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1482759702113400023105077 139008722073131252166101)
                ·
                  rfl

theorem cell20_913675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 5].length) (baseStart_913675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913675 prefixEnd_913675 := by exact prefixLift 913675
  have htrace : WordTrace (prefixWord ++ tailWord_913675) baseStart_913675 baseEnd_913675 := by
    simpa [prefixWord, tailWord_913675, baseEnd_913675] using wordTrace_append hprefix tailTrace_913675
  have hstable : (prefixWord ++ tailWord_913675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913675).length < 2 ^ (prefixWord ++ tailWord_913675).sum := by decide
  have hdescent : baseEnd_913675 < baseStart_913675 := by decide
  rcases family_descends (prefixWord ++ tailWord_913675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913709 : List Nat := [1, 5, 3, 1, 3, 7]
def baseStart_913709 : Nat := 118140960795 + 913709 * 2 ^ 59
def prefixEnd_913709 : Nat := 4983230072969 + 3 ^ 40 * 913709 * 2
def baseEnd_913709 : Nat := 15445988323920027754253

theorem tailTrace_913709 : CollatzResearch.WordTrace tailWord_913709 prefixEnd_913709 15445988323920027754253 := by
  unfold tailWord_913709
  simp only [CollatzResearch.WordTrace]
  refine ⟨33325705046795816918608181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22217136697863877945738787 33325705046795816918608181)
  ·
    refine ⟨3124284848137107836119517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33325705046795816918608181 3124284848137107836119517)
    ·
      refine ⟨1171606818051415438544819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3124284848137107836119517 1171606818051415438544819)
      ·
        refine ⟨1757410227077123157817229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1171606818051415438544819 1757410227077123157817229)
        ·
          refine ⟨659028835153921184181461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1757410227077123157817229 659028835153921184181461)
          ·
            refine ⟨15445988323920027754253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 659028835153921184181461 15445988323920027754253)
            ·
              rfl

theorem cell20_913709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 7].length) (baseStart_913709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913709 prefixEnd_913709 := by exact prefixLift 913709
  have htrace : WordTrace (prefixWord ++ tailWord_913709) baseStart_913709 baseEnd_913709 := by
    simpa [prefixWord, tailWord_913709, baseEnd_913709] using wordTrace_append hprefix tailTrace_913709
  have hstable : (prefixWord ++ tailWord_913709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913709).length < 2 ^ (prefixWord ++ tailWord_913709).sum := by decide
  have hdescent : baseEnd_913709 < baseStart_913709 := by decide
  rcases family_descends (prefixWord ++ tailWord_913709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913713 : List Nat := [1, 2, 2, 3, 4, 8]
def baseStart_913713 : Nat := 118140960795 + 913713 * 2 ^ 59
def prefixEnd_913713 : Nat := 4983230072969 + 3 ^ 40 * 913713 * 2
def baseEnd_913713 : Nat := 15446055942771648638203

theorem tailTrace_913713 : CollatzResearch.WordTrace tailWord_913713 prefixEnd_913713 15446055942771648638203 := by
  unfold tailWord_913713
  simp only [CollatzResearch.WordTrace]
  refine ⟨33325850938781325601753793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22217233959187550401169195 33325850938781325601753793)
  ·
    refine ⟨24994388204085994201315345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33325850938781325601753793 24994388204085994201315345)
    ·
      refine ⟨18745791153064495650986509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24994388204085994201315345 18745791153064495650986509)
      ·
        refine ⟨7029671682399185869119941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18745791153064495650986509 7029671682399185869119941)
        ·
          refine ⟨1318063440449847350459989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7029671682399185869119941 1318063440449847350459989)
          ·
            refine ⟨15446055942771648638203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1318063440449847350459989 15446055942771648638203)
            ·
              rfl

theorem cell20_913713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 8].length) (baseStart_913713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913713 prefixEnd_913713 := by exact prefixLift 913713
  have htrace : WordTrace (prefixWord ++ tailWord_913713) baseStart_913713 baseEnd_913713 := by
    simpa [prefixWord, tailWord_913713, baseEnd_913713] using wordTrace_append hprefix tailTrace_913713
  have hstable : (prefixWord ++ tailWord_913713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913713).length < 2 ^ (prefixWord ++ tailWord_913713).sum := by decide
  have hdescent : baseEnd_913713 < baseStart_913713 := by decide
  rcases family_descends (prefixWord ++ tailWord_913713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913716 : List Nat := [2, 5, 1, 1, 1, 2, 1, 4, 3]
def baseStart_913716 : Nat := 118140960795 + 913716 * 2 ^ 59
def prefixEnd_913716 : Nat := 4983230072969 + 3 ^ 40 * 913716 * 2
def baseEnd_913716 : Nat := 417044879736579836131469

theorem tailTrace_913716 : CollatzResearch.WordTrace tailWord_913716 prefixEnd_913716 417044879736579836131469 := by
  unfold tailWord_913716
  simp only [CollatzResearch.WordTrace]
  refine ⟨16662980178885228557056501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22217306905180304742742001 16662980178885228557056501)
  ·
    refine ⟨1562154391770490177224047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16662980178885228557056501 1562154391770490177224047)
    ·
      refine ⟨2343231587655735265836071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1562154391770490177224047 2343231587655735265836071)
      ·
        refine ⟨3514847381483602898754107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2343231587655735265836071 3514847381483602898754107)
        ·
          refine ⟨5272271072225404348131161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3514847381483602898754107 5272271072225404348131161)
          ·
            refine ⟨3954203304169053261098371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5272271072225404348131161 3954203304169053261098371)
            ·
              refine ⟨5931304956253579891647557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3954203304169053261098371 5931304956253579891647557)
              ·
                refine ⟨1112119679297546229683917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5931304956253579891647557 1112119679297546229683917)
                ·
                  refine ⟨417044879736579836131469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112119679297546229683917 417044879736579836131469)
                  ·
                    rfl

theorem cell20_913716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_913716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913716 prefixEnd_913716 := by exact prefixLift 913716
  have htrace : WordTrace (prefixWord ++ tailWord_913716) baseStart_913716 baseEnd_913716 := by
    simpa [prefixWord, tailWord_913716, baseEnd_913716] using wordTrace_append hprefix tailTrace_913716
  have hstable : (prefixWord ++ tailWord_913716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913716).length < 2 ^ (prefixWord ++ tailWord_913716).sum := by decide
  have hdescent : baseEnd_913716 < baseStart_913716 := by decide
  rcases family_descends (prefixWord ++ tailWord_913716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913720 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 5]
def baseStart_913720 : Nat := 118140960795 + 913720 * 2 ^ 59
def prefixEnd_913720 : Nat := 4983230072969 + 3 ^ 40 * 913720 * 2
def baseEnd_913720 : Nat := 417046705445573599998119

theorem tailTrace_913720 : CollatzResearch.WordTrace tailWord_913720 prefixEnd_913720 417046705445573599998119 := by
  unfold tailWord_913720
  simp only [CollatzResearch.WordTrace]
  refine ⟨16663053124877982898629307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22217404166503977198172409 16663053124877982898629307)
  ·
    refine ⟨24994579687316974347943961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16663053124877982898629307 24994579687316974347943961)
    ·
      refine ⟨18745934765487730760957971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24994579687316974347943961 18745934765487730760957971)
      ·
        refine ⟨28118902148231596141436957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18745934765487730760957971 28118902148231596141436957)
        ·
          refine ⟨10544588305586848553038859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28118902148231596141436957 10544588305586848553038859)
          ·
            refine ⟨15816882458380272829558289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10544588305586848553038859 15816882458380272829558289)
            ·
              refine ⟨11862661843785204622168717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15816882458380272829558289 11862661843785204622168717)
              ·
                refine ⟨4448498191419451733313269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11862661843785204622168717 4448498191419451733313269)
                ·
                  refine ⟨417046705445573599998119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4448498191419451733313269 417046705445573599998119)
                  ·
                    rfl

theorem cell20_913720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_913720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913720 prefixEnd_913720 := by exact prefixLift 913720
  have htrace : WordTrace (prefixWord ++ tailWord_913720) baseStart_913720 baseEnd_913720 := by
    simpa [prefixWord, tailWord_913720, baseEnd_913720] using wordTrace_append hprefix tailTrace_913720
  have hstable : (prefixWord ++ tailWord_913720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913720).length < 2 ^ (prefixWord ++ tailWord_913720).sum := by decide
  have hdescent : baseEnd_913720 < baseStart_913720 := by decide
  rcases family_descends (prefixWord ++ tailWord_913720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913744 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 4]
def baseStart_913744 : Nat := 118140960795 + 913744 * 2 ^ 59
def prefixEnd_913744 : Nat := 4983230072969 + 3 ^ 40 * 913744 * 2
def baseEnd_913744 : Nat := 417057659699536183198021

theorem tailTrace_913744 : CollatzResearch.WordTrace tailWord_913744 prefixEnd_913744 417057659699536183198021 := by
  unfold tailWord_913744
  simp only [CollatzResearch.WordTrace]
  refine ⟨16663490800834508948066143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22217987734446011930754857 16663490800834508948066143)
  ·
    refine ⟨24995236201251763422099215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16663490800834508948066143 24995236201251763422099215)
    ·
      refine ⟨37492854301877645133148823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24995236201251763422099215 37492854301877645133148823)
      ·
        refine ⟨56239281452816467699723235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37492854301877645133148823 56239281452816467699723235)
        ·
          refine ⟨84358922179224701549584853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56239281452816467699723235 84358922179224701549584853)
          ·
            refine ⟨1977162238575578942568395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 84358922179224701549584853 1977162238575578942568395)
            ·
              refine ⟨2965743357863368413852593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1977162238575578942568395 2965743357863368413852593)
              ·
                refine ⟨2224307518397526310389445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2965743357863368413852593 2224307518397526310389445)
                ·
                  refine ⟨417057659699536183198021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2224307518397526310389445 417057659699536183198021)
                  ·
                    rfl

theorem cell20_913744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_913744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913744 prefixEnd_913744 := by exact prefixLift 913744
  have htrace : WordTrace (prefixWord ++ tailWord_913744) baseStart_913744 baseEnd_913744 := by
    simpa [prefixWord, tailWord_913744, baseEnd_913744] using wordTrace_append hprefix tailTrace_913744
  have hstable : (prefixWord ++ tailWord_913744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913744).length < 2 ^ (prefixWord ++ tailWord_913744).sum := by decide
  have hdescent : baseEnd_913744 < baseStart_913744 := by decide
  rcases family_descends (prefixWord ++ tailWord_913744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913802 : List Nat := [3, 1, 2, 5, 1, 2, 2, 4]
def baseStart_913802 : Nat := 118140960795 + 913802 * 2 ^ 59
def prefixEnd_913802 : Nat := 4983230072969 + 3 ^ 40 * 913802 * 2
def baseEnd_913802 : Nat := 139028044159981919754817

theorem tailTrace_913802 : CollatzResearch.WordTrace tailWord_913802 prefixEnd_913802 139028044159981919754817 := by
  unfold tailWord_913802
  simp only [CollatzResearch.WordTrace]
  refine ⟨8332274258864723450435915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22219398023639262534495773 8332274258864723450435915)
  ·
    refine ⟨12498411388297085175653873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8332274258864723450435915 12498411388297085175653873)
    ·
      refine ⟨9373808541222813881740405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12498411388297085175653873 9373808541222813881740405)
      ·
        refine ⟨878794550739638801413163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9373808541222813881740405 878794550739638801413163)
        ·
          refine ⟨1318191826109458202119745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878794550739638801413163 1318191826109458202119745)
          ·
            refine ⟨988643869582093651589809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1318191826109458202119745 988643869582093651589809)
            ·
              refine ⟨741482902186570238692357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988643869582093651589809 741482902186570238692357)
              ·
                refine ⟨139028044159981919754817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 741482902186570238692357 139028044159981919754817)
                ·
                  rfl

theorem cell20_913802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_913802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913802 prefixEnd_913802 := by exact prefixLift 913802
  have htrace : WordTrace (prefixWord ++ tailWord_913802) baseStart_913802 baseEnd_913802 := by
    simpa [prefixWord, tailWord_913802, baseEnd_913802] using wordTrace_append hprefix tailTrace_913802
  have hstable : (prefixWord ++ tailWord_913802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913802).length < 2 ^ (prefixWord ++ tailWord_913802).sum := by decide
  have hdescent : baseEnd_913802 < baseStart_913802 := by decide
  rcases family_descends (prefixWord ++ tailWord_913802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913806 : List Nat := [4, 1, 1, 4, 1, 2, 1, 6]
def baseStart_913806 : Nat := 118140960795 + 913806 * 2 ^ 59
def prefixEnd_913806 : Nat := 4983230072969 + 3 ^ 40 * 913806 * 2
def baseEnd_913806 : Nat := 139028652729646507710367

theorem tailTrace_913806 : CollatzResearch.WordTrace tailWord_913806 prefixEnd_913806 139028652729646507710367 := by
  unfold tailWord_913806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4166155365930550310611159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22219495284962934989926181 4166155365930550310611159)
  ·
    refine ⟨6249233048895825465916739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4166155365930550310611159 6249233048895825465916739)
    ·
      refine ⟨9373849573343738198875109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6249233048895825465916739 9373849573343738198875109)
      ·
        refine ⟨1757596795001950912289083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9373849573343738198875109 1757596795001950912289083)
        ·
          refine ⟨2636395192502926368433625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1757596795001950912289083 2636395192502926368433625)
          ·
            refine ⟨1977296394377194776325219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2636395192502926368433625 1977296394377194776325219)
            ·
              refine ⟨2965944591565792164487829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1977296394377194776325219 2965944591565792164487829)
              ·
                refine ⟨139028652729646507710367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2965944591565792164487829 139028652729646507710367)
                ·
                  rfl

theorem cell20_913806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_913806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913806 prefixEnd_913806 := by exact prefixLift 913806
  have htrace : WordTrace (prefixWord ++ tailWord_913806) baseStart_913806 baseEnd_913806 := by
    simpa [prefixWord, tailWord_913806, baseEnd_913806] using wordTrace_append hprefix tailTrace_913806
  have hstable : (prefixWord ++ tailWord_913806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913806).length < 2 ^ (prefixWord ++ tailWord_913806).sum := by decide
  have hdescent : baseEnd_913806 < baseStart_913806 := by decide
  rcases family_descends (prefixWord ++ tailWord_913806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913812 : List Nat := [2, 4, 2, 1, 4, 1, 1, 3, 2]
def baseStart_913812 : Nat := 118140960795 + 913812 * 2 ^ 59
def prefixEnd_913812 : Nat := 4983230072969 + 3 ^ 40 * 913812 * 2
def baseEnd_913812 : Nat := 417088696752430168931077

theorem tailTrace_913812 : CollatzResearch.WordTrace tailWord_913812 prefixEnd_913812 417088696752430168931077 := by
  unfold tailWord_913812
  simp only [CollatzResearch.WordTrace]
  refine ⟨16664730882711332754803845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22219641176948443673071793 16664730882711332754803845)
  ·
    refine ⟨3124637040508374891525721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16664730882711332754803845 3124637040508374891525721)
    ·
      refine ⟨2343477780381281168644291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3124637040508374891525721 2343477780381281168644291)
      ·
        refine ⟨3515216670571921752966437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2343477780381281168644291 3515216670571921752966437)
        ·
          refine ⟨659103125732235328681207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3515216670571921752966437 659103125732235328681207)
          ·
            refine ⟨988654688598352993021811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659103125732235328681207 988654688598352993021811)
            ·
              refine ⟨1482982032897529489532717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 988654688598352993021811 1482982032897529489532717)
              ·
                refine ⟨556118262336573558574769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1482982032897529489532717 556118262336573558574769)
                ·
                  refine ⟨417088696752430168931077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556118262336573558574769 417088696752430168931077)
                  ·
                    rfl

theorem cell20_913812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_913812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913812 prefixEnd_913812 := by exact prefixLift 913812
  have htrace : WordTrace (prefixWord ++ tailWord_913812) baseStart_913812 baseEnd_913812 := by
    simpa [prefixWord, tailWord_913812, baseEnd_913812] using wordTrace_append hprefix tailTrace_913812
  have hstable : (prefixWord ++ tailWord_913812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913812).length < 2 ^ (prefixWord ++ tailWord_913812).sum := by decide
  have hdescent : baseEnd_913812 < baseStart_913812 := by decide
  rcases family_descends (prefixWord ++ tailWord_913812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913816 : List Nat := [2, 1, 2, 5, 1, 1, 3, 3, 2]
def baseStart_913816 : Nat := 118140960795 + 913816 * 2 ^ 59
def prefixEnd_913816 : Nat := 4983230072969 + 3 ^ 40 * 913816 * 2
def baseEnd_913816 : Nat := 417090522461423932797727

theorem tailTrace_913816 : CollatzResearch.WordTrace tailWord_913816 prefixEnd_913816 417090522461423932797727 := by
  unfold tailWord_913816
  simp only [CollatzResearch.WordTrace]
  refine ⟨16664803828704087096376651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22219738438272116128502201 16664803828704087096376651)
  ·
    refine ⟨24997205743056130644564977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16664803828704087096376651 24997205743056130644564977)
    ·
      refine ⟨18747904307292097983423733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24997205743056130644564977 18747904307292097983423733)
      ·
        refine ⟨1757616028808634185945975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18747904307292097983423733 1757616028808634185945975)
        ·
          refine ⟨2636424043212951278918963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1757616028808634185945975 2636424043212951278918963)
          ·
            refine ⟨3954636064819426918378445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636424043212951278918963 3954636064819426918378445)
            ·
              refine ⟨1482988524307285094391917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3954636064819426918378445 1482988524307285094391917)
              ·
                refine ⟨556120696615231910396969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1482988524307285094391917 556120696615231910396969)
                ·
                  refine ⟨417090522461423932797727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556120696615231910396969 417090522461423932797727)
                  ·
                    rfl

theorem cell20_913816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 2].length) (baseStart_913816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913816 prefixEnd_913816 := by exact prefixLift 913816
  have htrace : WordTrace (prefixWord ++ tailWord_913816) baseStart_913816 baseEnd_913816 := by
    simpa [prefixWord, tailWord_913816, baseEnd_913816] using wordTrace_append hprefix tailTrace_913816
  have hstable : (prefixWord ++ tailWord_913816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913816).length < 2 ^ (prefixWord ++ tailWord_913816).sum := by decide
  have hdescent : baseEnd_913816 < baseStart_913816 := by decide
  rcases family_descends (prefixWord ++ tailWord_913816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913827 : List Nat := [1, 1, 1, 4, 1, 6, 6]
def baseStart_913827 : Nat := 118140960795 + 913827 * 2 ^ 59
def prefixEnd_913827 : Nat := 4983230072969 + 3 ^ 40 * 913827 * 2
def baseEnd_913827 : Nat := 46343949240128531492335

theorem tailTrace_913827 : CollatzResearch.WordTrace tailWord_913827 prefixEnd_913827 46343949240128531492335 := by
  unfold tailWord_913827
  simp only [CollatzResearch.WordTrace]
  refine ⟨33330008860368323071403735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22220005906912215380935823 33330008860368323071403735)
  ·
    refine ⟨49995013290552484607105603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33330008860368323071403735 49995013290552484607105603)
    ·
      refine ⟨74992519935828726910658405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49995013290552484607105603 74992519935828726910658405)
      ·
        refine ⟨14061097487967886295748451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74992519935828726910658405 14061097487967886295748451)
        ·
          refine ⟨21091646231951829443622677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14061097487967886295748451 21091646231951829443622677)
          ·
            refine ⟨988670917122742005169813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21091646231951829443622677 988670917122742005169813)
            ·
              refine ⟨46343949240128531492335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 988670917122742005169813 46343949240128531492335)
              ·
                rfl

theorem cell20_913827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 6].length) (baseStart_913827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913827 prefixEnd_913827 := by exact prefixLift 913827
  have htrace : WordTrace (prefixWord ++ tailWord_913827) baseStart_913827 baseEnd_913827 := by
    simpa [prefixWord, tailWord_913827, baseEnd_913827] using wordTrace_append hprefix tailTrace_913827
  have hstable : (prefixWord ++ tailWord_913827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913827).length < 2 ^ (prefixWord ++ tailWord_913827).sum := by decide
  have hdescent : baseEnd_913827 < baseStart_913827 := by decide
  rcases family_descends (prefixWord ++ tailWord_913827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913889 : List Nat := [1, 2, 3, 1, 2, 2, 4, 2, 3]
def baseStart_913889 : Nat := 118140960795 + 913889 * 2 ^ 59
def prefixEnd_913889 : Nat := 4983230072969 + 3 ^ 40 * 913889 * 2
def baseEnd_913889 : Nat := 417123841650560123364095

theorem tailTrace_913889 : CollatzResearch.WordTrace tailWord_913889 prefixEnd_913889 417123841650560123364095 := by
  unfold tailWord_913889
  simp only [CollatzResearch.WordTrace]
  refine ⟨33332270186143707660160721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22221513457429138440107147 33332270186143707660160721)
  ·
    refine ⟨24999202639607780745120541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33332270186143707660160721 24999202639607780745120541)
    ·
      refine ⟨9374700989852917779420203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24999202639607780745120541 9374700989852917779420203)
      ·
        refine ⟨14062051484779376669130305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9374700989852917779420203 14062051484779376669130305)
        ·
          refine ⟨10546538613584532501847729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14062051484779376669130305 10546538613584532501847729)
          ·
            refine ⟨7909903960188399376385797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10546538613584532501847729 7909903960188399376385797)
            ·
              refine ⟨1483106992535324883072337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7909903960188399376385797 1483106992535324883072337)
              ·
                refine ⟨1112330244401493662304253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1483106992535324883072337 1112330244401493662304253)
                ·
                  refine ⟨417123841650560123364095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112330244401493662304253 417123841650560123364095)
                  ·
                    rfl

theorem cell20_913889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_913889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913889 prefixEnd_913889 := by exact prefixLift 913889
  have htrace : WordTrace (prefixWord ++ tailWord_913889) baseStart_913889 baseEnd_913889 := by
    simpa [prefixWord, tailWord_913889, baseEnd_913889] using wordTrace_append hprefix tailTrace_913889
  have hstable : (prefixWord ++ tailWord_913889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913889).length < 2 ^ (prefixWord ++ tailWord_913889).sum := by decide
  have hdescent : baseEnd_913889 < baseStart_913889 := by decide
  rcases family_descends (prefixWord ++ tailWord_913889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913926 : List Nat := [6, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_913926 : Nat := 118140960795 + 913926 * 2 ^ 59
def prefixEnd_913926 : Nat := 4983230072969 + 3 ^ 40 * 913926 * 2
def baseEnd_913926 : Nat := 417140729458752439130611

theorem tailTrace_913926 : CollatzResearch.WordTrace tailWord_913926 prefixEnd_913926 417140729458752439130611 := by
  unfold tailWord_913926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1041675615219051968101801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22222413124673108652838421 1041675615219051968101801)
  ·
    refine ⟨781256711414288976076351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1041675615219051968101801 781256711414288976076351)
    ·
      refine ⟨1171885067121433464114527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 781256711414288976076351 1171885067121433464114527)
      ·
        refine ⟨1757827600682150196171791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1171885067121433464114527 1757827600682150196171791)
        ·
          refine ⟨2636741401023225294257687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1757827600682150196171791 2636741401023225294257687)
          ·
            refine ⟨3955112101534837941386531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636741401023225294257687 3955112101534837941386531)
            ·
              refine ⟨5932668152302256912079797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3955112101534837941386531 5932668152302256912079797)
              ·
                refine ⟨556187639278336585507481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5932668152302256912079797 556187639278336585507481)
                ·
                  refine ⟨417140729458752439130611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556187639278336585507481 417140729458752439130611)
                  ·
                    rfl

theorem cell20_913926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_913926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913926 prefixEnd_913926 := by exact prefixLift 913926
  have htrace : WordTrace (prefixWord ++ tailWord_913926) baseStart_913926 baseEnd_913926 := by
    simpa [prefixWord, tailWord_913926, baseEnd_913926] using wordTrace_append hprefix tailTrace_913926
  have hstable : (prefixWord ++ tailWord_913926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913926).length < 2 ^ (prefixWord ++ tailWord_913926).sum := by decide
  have hdescent : baseEnd_913926 < baseStart_913926 := by decide
  rcases family_descends (prefixWord ++ tailWord_913926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913944 : List Nat := [2, 1, 2, 3, 3, 3, 1, 2, 3]
def baseStart_913944 : Nat := 118140960795 + 913944 * 2 ^ 59
def prefixEnd_913944 : Nat := 4983230072969 + 3 ^ 40 * 913944 * 2
def baseEnd_913944 : Nat := 417148945149224376530537

theorem tailTrace_913944 : CollatzResearch.WordTrace tailWord_913944 prefixEnd_913944 417148945149224376530537 := by
  unfold tailWord_913944
  simp only [CollatzResearch.WordTrace]
  refine ⟨16667138100472226026706443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22222850800629634702275257 16667138100472226026706443)
  ·
    refine ⟨25000707150708339040059665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16667138100472226026706443 25000707150708339040059665)
    ·
      refine ⟨18750530363031254280044749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25000707150708339040059665 18750530363031254280044749)
      ·
        refine ⟨7031448886136720355016781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18750530363031254280044749 7031448886136720355016781)
        ·
          refine ⟨2636793332301270133131293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7031448886136720355016781 2636793332301270133131293)
          ·
            refine ⟨988797499612976299924235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2636793332301270133131293 988797499612976299924235)
            ·
              refine ⟨1483196249419464449886353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 988797499612976299924235 1483196249419464449886353)
              ·
                refine ⟨1112397187064598337414765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1483196249419464449886353 1112397187064598337414765)
                ·
                  refine ⟨417148945149224376530537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112397187064598337414765 417148945149224376530537)
                  ·
                    rfl

theorem cell20_913944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_913944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913944 prefixEnd_913944 := by exact prefixLift 913944
  have htrace : WordTrace (prefixWord ++ tailWord_913944) baseStart_913944 baseEnd_913944 := by
    simpa [prefixWord, tailWord_913944, baseEnd_913944] using wordTrace_append hprefix tailTrace_913944
  have hstable : (prefixWord ++ tailWord_913944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913944).length < 2 ^ (prefixWord ++ tailWord_913944).sum := by decide
  have hdescent : baseEnd_913944 < baseStart_913944 := by decide
  rcases family_descends (prefixWord ++ tailWord_913944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913989 : List Nat := [1, 3, 1, 1, 1, 5, 3, 3, 2]
def baseStart_913989 : Nat := 118140960795 + 913989 * 2 ^ 59
def prefixEnd_913989 : Nat := 4983230072969 + 3 ^ 40 * 913989 * 2
def baseEnd_913989 : Nat := 417169484375404220030353

theorem tailTrace_913989 : CollatzResearch.WordTrace tailWord_913989 prefixEnd_913989 417169484375404220030353 := by
  unfold tailWord_913989
  simp only [CollatzResearch.WordTrace]
  refine ⟨33335917485781424738801021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22223944990520949825867347 33335917485781424738801021)
  ·
    refine ⟨12500969057168034277050383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33335917485781424738801021 12500969057168034277050383)
    ·
      refine ⟨18751453585752051415575575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12500969057168034277050383 18751453585752051415575575)
      ·
        refine ⟨28127180378628077123363363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18751453585752051415575575 28127180378628077123363363)
        ·
          refine ⟨42190770567942115685045045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28127180378628077123363363 42190770567942115685045045)
          ·
            refine ⟨3955384740744573345472973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42190770567942115685045045 3955384740744573345472973)
            ·
              refine ⟨1483269277779215004552365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3955384740744573345472973 1483269277779215004552365)
              ·
                refine ⟨556225979167205626707137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1483269277779215004552365 556225979167205626707137)
                ·
                  refine ⟨417169484375404220030353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556225979167205626707137 417169484375404220030353)
                  ·
                    rfl

theorem cell20_913989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_913989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_913989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_913989 prefixEnd_913989 := by exact prefixLift 913989
  have htrace : WordTrace (prefixWord ++ tailWord_913989) baseStart_913989 baseEnd_913989 := by
    simpa [prefixWord, tailWord_913989, baseEnd_913989] using wordTrace_append hprefix tailTrace_913989
  have hstable : (prefixWord ++ tailWord_913989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913989).length < 2 ^ (prefixWord ++ tailWord_913989).sum := by decide
  have hdescent : baseEnd_913989 < baseStart_913989 := by decide
  rcases family_descends (prefixWord ++ tailWord_913989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914017 : List Nat := [1, 2, 3, 1, 1, 5, 2, 5]
def baseStart_914017 : Nat := 118140960795 + 914017 * 2 ^ 59
def prefixEnd_914017 : Nat := 4983230072969 + 3 ^ 40 * 914017 * 2
def baseEnd_914017 : Nat := 139060754779453522365635

theorem tailTrace_914017 : CollatzResearch.WordTrace tailWord_914017 prefixEnd_914017 139060754779453522365635 := by
  unfold tailWord_914017
  simp only [CollatzResearch.WordTrace]
  refine ⟨33336938729679985520820305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22224625819786657013880203 33336938729679985520820305)
  ·
    refine ⟨25002704047259989140615229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33336938729679985520820305 25002704047259989140615229)
    ·
      refine ⟨9376014017722495927730711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25002704047259989140615229 9376014017722495927730711)
      ·
        refine ⟨14064021026583743891596067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9376014017722495927730711 14064021026583743891596067)
        ·
          refine ⟨21096031539875615837394101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14064021026583743891596067 21096031539875615837394101)
          ·
            refine ⟨1977752956863338984755697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21096031539875615837394101 1977752956863338984755697)
            ·
              refine ⟨1483314717647504238566773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1977752956863338984755697 1483314717647504238566773)
              ·
                refine ⟨139060754779453522365635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1483314717647504238566773 139060754779453522365635)
                ·
                  rfl

theorem cell20_914017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 5].length) (baseStart_914017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914017 prefixEnd_914017 := by exact prefixLift 914017
  have htrace : WordTrace (prefixWord ++ tailWord_914017) baseStart_914017 baseEnd_914017 := by
    simpa [prefixWord, tailWord_914017, baseEnd_914017] using wordTrace_append hprefix tailTrace_914017
  have hstable : (prefixWord ++ tailWord_914017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914017).length < 2 ^ (prefixWord ++ tailWord_914017).sum := by decide
  have hdescent : baseEnd_914017 < baseStart_914017 := by decide
  rcases family_descends (prefixWord ++ tailWord_914017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914031 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 4]
def baseStart_914031 : Nat := 118140960795 + 914031 * 2 ^ 59
def prefixEnd_914031 : Nat := 4983230072969 + 3 ^ 40 * 914031 * 2
def baseEnd_914031 : Nat := 417188654319838740630181

theorem tailTrace_914031 : CollatzResearch.WordTrace tailWord_914031 prefixEnd_914031 417188654319838740630181 := by
  unfold tailWord_914031
  simp only [CollatzResearch.WordTrace]
  refine ⟨33337449351629265911829947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22224966234419510607886631 33337449351629265911829947)
  ·
    refine ⟨50006174027443898867744921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33337449351629265911829947 50006174027443898867744921)
    ·
      refine ⟨37504630520582924150808691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50006174027443898867744921 37504630520582924150808691)
      ·
        refine ⟨56256945780874386226213037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37504630520582924150808691 56256945780874386226213037)
        ·
          refine ⟨21096354667827894834829889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56256945780874386226213037 21096354667827894834829889)
          ·
            refine ⟨15822266000870921126122417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21096354667827894834829889 15822266000870921126122417)
            ·
              refine ⟨11866699500653190844591813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15822266000870921126122417 11866699500653190844591813)
              ·
                refine ⟨2225006156372473283360965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11866699500653190844591813 2225006156372473283360965)
                ·
                  refine ⟨417188654319838740630181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2225006156372473283360965 417188654319838740630181)
                  ·
                    rfl

theorem cell20_914031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_914031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914031 prefixEnd_914031 := by exact prefixLift 914031
  have htrace : WordTrace (prefixWord ++ tailWord_914031) baseStart_914031 baseEnd_914031 := by
    simpa [prefixWord, tailWord_914031, baseEnd_914031] using wordTrace_append hprefix tailTrace_914031
  have hstable : (prefixWord ++ tailWord_914031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914031).length < 2 ^ (prefixWord ++ tailWord_914031).sum := by decide
  have hdescent : baseEnd_914031 < baseStart_914031 := by decide
  rcases family_descends (prefixWord ++ tailWord_914031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914058 : List Nat := [3, 1, 2, 3, 3, 1, 2, 2, 3]
def baseStart_914058 : Nat := 118140960795 + 914058 * 2 ^ 59
def prefixEnd_914058 : Nat := 4983230072969 + 3 ^ 40 * 914058 * 2
def baseEnd_914058 : Nat := 417200977855546646730071

theorem tailTrace_914058 : CollatzResearch.WordTrace tailWord_914058 prefixEnd_914058 417200977855546646730071 := by
  unfold tailWord_914058
  simp only [CollatzResearch.WordTrace]
  refine ⟨8334608530632862380765707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22225622748354299682041885 8334608530632862380765707)
  ·
    refine ⟨12501912795949293571148561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8334608530632862380765707 12501912795949293571148561)
    ·
      refine ⟨9376434596961970178361421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12501912795949293571148561 9376434596961970178361421)
      ·
        refine ⟨3516162973860738816885533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9376434596961970178361421 3516162973860738816885533)
        ·
          refine ⟨1318561115197777056332075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3516162973860738816885533 1318561115197777056332075)
          ·
            refine ⟨1977841672796665584498113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318561115197777056332075 1977841672796665584498113)
            ·
              refine ⟨1483381254597499188373585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1977841672796665584498113 1483381254597499188373585)
              ·
                refine ⟨1112535940948124391280189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1483381254597499188373585 1112535940948124391280189)
                ·
                  refine ⟨417200977855546646730071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112535940948124391280189 417200977855546646730071)
                  ·
                    rfl

theorem cell20_914058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_914058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914058 prefixEnd_914058 := by exact prefixLift 914058
  have htrace : WordTrace (prefixWord ++ tailWord_914058) baseStart_914058 baseEnd_914058 := by
    simpa [prefixWord, tailWord_914058, baseEnd_914058] using wordTrace_append hprefix tailTrace_914058
  have hstable : (prefixWord ++ tailWord_914058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914058).length < 2 ^ (prefixWord ++ tailWord_914058).sum := by decide
  have hdescent : baseEnd_914058 < baseStart_914058 := by decide
  rcases family_descends (prefixWord ++ tailWord_914058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914124 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 4]
def baseStart_914124 : Nat := 118140960795 + 914124 * 2 ^ 59
def prefixEnd_914124 : Nat := 4983230072969 + 3 ^ 40 * 914124 * 2
def baseEnd_914124 : Nat := 417231102053943750529801

theorem tailTrace_914124 : CollatzResearch.WordTrace tailWord_914124 prefixEnd_914124 417231102053943750529801 := by
  unfold tailWord_914124
  simp only [CollatzResearch.WordTrace]
  refine ⟨16670420670146171397482713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22227227560194895196643617 16670420670146171397482713)
  ·
    refine ⟨12502815502609628548112035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16670420670146171397482713 12502815502609628548112035)
    ·
      refine ⟨18754223253914442822168053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12502815502609628548112035 18754223253914442822168053)
      ·
        refine ⟨1758208430054479014578255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18754223253914442822168053 1758208430054479014578255)
        ·
          refine ⟨2637312645081718521867383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1758208430054479014578255 2637312645081718521867383)
          ·
            refine ⟨3955968967622577782801075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637312645081718521867383 3955968967622577782801075)
            ·
              refine ⟨5933953451433866674201613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3955968967622577782801075 5933953451433866674201613)
              ·
                refine ⟨2225232544287700002825605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5933953451433866674201613 2225232544287700002825605)
                ·
                  refine ⟨417231102053943750529801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2225232544287700002825605 417231102053943750529801)
                  ·
                    rfl

theorem cell20_914124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_914124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914124 prefixEnd_914124 := by exact prefixLift 914124
  have htrace : WordTrace (prefixWord ++ tailWord_914124) baseStart_914124 baseEnd_914124 := by
    simpa [prefixWord, tailWord_914124, baseEnd_914124] using wordTrace_append hprefix tailTrace_914124
  have hstable : (prefixWord ++ tailWord_914124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914124).length < 2 ^ (prefixWord ++ tailWord_914124).sum := by decide
  have hdescent : baseEnd_914124 < baseStart_914124 := by decide
  rcases family_descends (prefixWord ++ tailWord_914124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914148 : List Nat := [2, 3, 1, 1, 1, 6, 2, 4]
def baseStart_914148 : Nat := 118140960795 + 914148 * 2 ^ 59
def prefixEnd_914148 : Nat := 4983230072969 + 3 ^ 40 * 914148 * 2
def baseEnd_914148 : Nat := 139080685435968777909901

theorem tailTrace_914148 : CollatzResearch.WordTrace tailWord_914148 prefixEnd_914148 139080685435968777909901 := by
  unfold tailWord_914148
  simp only [CollatzResearch.WordTrace]
  refine ⟨16670858346102697446919549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22227811128136929929226065 16670858346102697446919549)
  ·
    refine ⟨6251571879788511542594831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16670858346102697446919549 6251571879788511542594831)
    ·
      refine ⟨9377357819682767313892247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6251571879788511542594831 9377357819682767313892247)
      ·
        refine ⟨14066036729524150970838371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9377357819682767313892247 14066036729524150970838371)
        ·
          refine ⟨21099055094286226456257557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14066036729524150970838371 21099055094286226456257557)
          ·
            refine ⟨989018207544666865137073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21099055094286226456257557 989018207544666865137073)
            ·
              refine ⟨741763655658500148852805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 989018207544666865137073 741763655658500148852805)
              ·
                refine ⟨139080685435968777909901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 741763655658500148852805 139080685435968777909901)
                ·
                  rfl

theorem cell20_914148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_914148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914148 prefixEnd_914148 := by exact prefixLift 914148
  have htrace : WordTrace (prefixWord ++ tailWord_914148) baseStart_914148 baseEnd_914148 := by
    simpa [prefixWord, tailWord_914148, baseEnd_914148] using wordTrace_append hprefix tailTrace_914148
  have hstable : (prefixWord ++ tailWord_914148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914148).length < 2 ^ (prefixWord ++ tailWord_914148).sum := by decide
  have hdescent : baseEnd_914148 < baseStart_914148 := by decide
  rcases family_descends (prefixWord ++ tailWord_914148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914158 : List Nat := [4, 1, 2, 1, 1, 5, 1, 3, 2]
def baseStart_914158 : Nat := 118140960795 + 914158 * 2 ^ 59
def prefixEnd_914158 : Nat := 4983230072969 + 3 ^ 40 * 914158 * 2
def baseEnd_914158 : Nat := 417246620580390743396329

theorem tailTrace_914158 : CollatzResearch.WordTrace tailWord_914158 prefixEnd_914158 417246620580390743396329 := by
  unfold tailWord_914158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4167760177771145825212891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22228054281446111067802085 4167760177771145825212891)
  ·
    refine ⟨6251640266656718737819337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4167760177771145825212891 6251640266656718737819337)
    ·
      refine ⟨4688730199992539053364503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6251640266656718737819337 4688730199992539053364503)
      ·
        refine ⟨7033095299988808580046755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4688730199992539053364503 7033095299988808580046755)
        ·
          refine ⟨10549642949983212870070133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7033095299988808580046755 10549642949983212870070133)
          ·
            refine ⟨989029026560926206569075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10549642949983212870070133 989029026560926206569075)
            ·
              refine ⟨1483543539841389309853613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989029026560926206569075 1483543539841389309853613)
              ·
                refine ⟨556328827440520991195105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1483543539841389309853613 556328827440520991195105)
                ·
                  refine ⟨417246620580390743396329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556328827440520991195105 417246620580390743396329)
                  ·
                    rfl

theorem cell20_914158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_914158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914158 prefixEnd_914158 := by exact prefixLift 914158
  have htrace : WordTrace (prefixWord ++ tailWord_914158) baseStart_914158 baseEnd_914158 := by
    simpa [prefixWord, tailWord_914158, baseEnd_914158] using wordTrace_append hprefix tailTrace_914158
  have hstable : (prefixWord ++ tailWord_914158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914158).length < 2 ^ (prefixWord ++ tailWord_914158).sum := by decide
  have hdescent : baseEnd_914158 < baseStart_914158 := by decide
  rcases family_descends (prefixWord ++ tailWord_914158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914193 : List Nat := [1, 2, 2, 1, 1, 3, 6, 1, 3]
def baseStart_914193 : Nat := 118140960795 + 914193 * 2 ^ 59
def prefixEnd_914193 : Nat := 4983230072969 + 3 ^ 40 * 914193 * 2
def baseEnd_914193 : Nat := 417262595534086177229519

theorem tailTrace_914193 : CollatzResearch.WordTrace tailWord_914193 prefixEnd_914193 417262595534086177229519 := by
  unfold tailWord_914193
  simp only [CollatzResearch.WordTrace]
  refine ⟨33343357977042367579227233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22228905318028245052818155 33343357977042367579227233)
  ·
    refine ⟨25007518482781775684420425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33343357977042367579227233 25007518482781775684420425)
    ·
      refine ⟨18755638862086331763315319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25007518482781775684420425 18755638862086331763315319)
      ·
        refine ⟨28133458293129497644972979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18755638862086331763315319 28133458293129497644972979)
        ·
          refine ⟨42200187439694246467459469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28133458293129497644972979 42200187439694246467459469)
          ·
            refine ⟨15825070289885342425297301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42200187439694246467459469 15825070289885342425297301)
            ·
              refine ⟨741800169838375426185811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15825070289885342425297301 741800169838375426185811)
              ·
                refine ⟨1112700254757563139278717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741800169838375426185811 1112700254757563139278717)
                ·
                  refine ⟨417262595534086177229519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112700254757563139278717 417262595534086177229519)
                  ·
                    rfl

theorem cell20_914193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 3].length) (baseStart_914193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914193 prefixEnd_914193 := by exact prefixLift 914193
  have htrace : WordTrace (prefixWord ++ tailWord_914193) baseStart_914193 baseEnd_914193 := by
    simpa [prefixWord, tailWord_914193, baseEnd_914193] using wordTrace_append hprefix tailTrace_914193
  have hstable : (prefixWord ++ tailWord_914193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914193).length < 2 ^ (prefixWord ++ tailWord_914193).sum := by decide
  have hdescent : baseEnd_914193 < baseStart_914193 := by decide
  rcases family_descends (prefixWord ++ tailWord_914193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914230 : List Nat := [5, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_914230 : Nat := 118140960795 + 914230 * 2 ^ 59
def prefixEnd_914230 : Nat := 4983230072969 + 3 ^ 40 * 914230 * 2
def baseEnd_914230 : Nat := 417279483342278492996035

theorem tailTrace_914230 : CollatzResearch.WordTrace tailWord_914230 prefixEnd_914230 417279483342278492996035 := by
  unfold tailWord_914230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2084044217369270181145259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22229804985272215265549429 2084044217369270181145259)
  ·
    refine ⟨3126066326053905271717889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2084044217369270181145259 3126066326053905271717889)
    ·
      refine ⟨2344549744540428953788417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3126066326053905271717889 2344549744540428953788417)
      ·
        refine ⟨1758412308405321715341313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2344549744540428953788417 1758412308405321715341313)
        ·
          refine ⟨1318809231303991286505985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1758412308405321715341313 1318809231303991286505985)
          ·
            refine ⟨989106923477993464879489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1318809231303991286505985 989106923477993464879489)
            ·
              refine ⟨741830192608495098659617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 989106923477993464879489 741830192608495098659617)
              ·
                refine ⟨556372644456371323994713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741830192608495098659617 556372644456371323994713)
                ·
                  refine ⟨417279483342278492996035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556372644456371323994713 417279483342278492996035)
                  ·
                    rfl

theorem cell20_914230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_914230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914230 prefixEnd_914230 := by exact prefixLift 914230
  have htrace : WordTrace (prefixWord ++ tailWord_914230) baseStart_914230 baseEnd_914230 := by
    simpa [prefixWord, tailWord_914230, baseEnd_914230] using wordTrace_append hprefix tailTrace_914230
  have hstable : (prefixWord ++ tailWord_914230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914230).length < 2 ^ (prefixWord ++ tailWord_914230).sum := by decide
  have hdescent : baseEnd_914230 < baseStart_914230 := by decide
  rcases family_descends (prefixWord ++ tailWord_914230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914241 : List Nat := [1, 2, 5, 3, 1, 2, 1, 5]
def baseStart_914241 : Nat := 118140960795 + 914241 * 2 ^ 59
def prefixEnd_914241 : Nat := 4983230072969 + 3 ^ 40 * 914241 * 2
def baseEnd_914241 : Nat := 139094834680670447876441

theorem tailTrace_914241 : CollatzResearch.WordTrace tailWord_914241 prefixEnd_914241 139094834680670447876441 := by
  unfold tailWord_914241
  simp only [CollatzResearch.WordTrace]
  refine ⟨33345108680868471776974577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22230072453912314517983051 33345108680868471776974577)
  ·
    refine ⟨25008831510651353832730933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33345108680868471776974577 25008831510651353832730933)
    ·
      refine ⟨2344577954123564421818525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25008831510651353832730933 2344577954123564421818525)
      ·
        refine ⟨879216732796336658181947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2344577954123564421818525 879216732796336658181947)
        ·
          refine ⟨1318825099194504987272921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879216732796336658181947 1318825099194504987272921)
          ·
            refine ⟨989118824395878740454691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1318825099194504987272921 989118824395878740454691)
            ·
              refine ⟨1483678236593818110682037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989118824395878740454691 1483678236593818110682037)
              ·
                refine ⟨139094834680670447876441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1483678236593818110682037 139094834680670447876441)
                ·
                  rfl

theorem cell20_914241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 5].length) (baseStart_914241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914241 prefixEnd_914241 := by exact prefixLift 914241
  have htrace : WordTrace (prefixWord ++ tailWord_914241) baseStart_914241 baseEnd_914241 := by
    simpa [prefixWord, tailWord_914241, baseEnd_914241] using wordTrace_append hprefix tailTrace_914241
  have hstable : (prefixWord ++ tailWord_914241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914241).length < 2 ^ (prefixWord ++ tailWord_914241).sum := by decide
  have hdescent : baseEnd_914241 < baseStart_914241 := by decide
  rcases family_descends (prefixWord ++ tailWord_914241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914293 : List Nat := [1, 3, 4, 1, 1, 2, 2, 4, 2]
def baseStart_914293 : Nat := 118140960795 + 914293 * 2 ^ 59
def prefixEnd_914293 : Nat := 4983230072969 + 3 ^ 40 * 914293 * 2
def baseEnd_914293 : Nat := 417308238258930273895777

theorem tailTrace_914293 : CollatzResearch.WordTrace tailWord_914293 prefixEnd_914293 417308238258930273895777 := by
  unfold tailWord_914293
  simp only [CollatzResearch.WordTrace]
  refine ⟨33347005276680084657867533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22231336851120056438578355 33347005276680084657867533)
  ·
    refine ⟨12505126978755031746700325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33347005276680084657867533 12505126978755031746700325)
    ·
      refine ⟨2344711308516568452506311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12505126978755031746700325 2344711308516568452506311)
      ·
        refine ⟨3517066962774852678759467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2344711308516568452506311 3517066962774852678759467)
        ·
          refine ⟨5275600444162279018139201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3517066962774852678759467 5275600444162279018139201)
          ·
            refine ⟨3956700333121709263604401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5275600444162279018139201 3956700333121709263604401)
            ·
              refine ⟨2967525249841281947703301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3956700333121709263604401 2967525249841281947703301)
              ·
                refine ⟨556410984345240365194369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2967525249841281947703301 556410984345240365194369)
                ·
                  refine ⟨417308238258930273895777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556410984345240365194369 417308238258930273895777)
                  ·
                    rfl

theorem cell20_914293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_914293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914293 prefixEnd_914293 := by exact prefixLift 914293
  have htrace : WordTrace (prefixWord ++ tailWord_914293) baseStart_914293 baseEnd_914293 := by
    simpa [prefixWord, tailWord_914293, baseEnd_914293] using wordTrace_append hprefix tailTrace_914293
  have hstable : (prefixWord ++ tailWord_914293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914293).length < 2 ^ (prefixWord ++ tailWord_914293).sum := by decide
  have hdescent : baseEnd_914293 < baseStart_914293 := by decide
  rcases family_descends (prefixWord ++ tailWord_914293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914297 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 4]
def baseStart_914297 : Nat := 118140960795 + 914297 * 2 ^ 59
def prefixEnd_914297 : Nat := 4983230072969 + 3 ^ 40 * 914297 * 2
def baseEnd_914297 : Nat := 417310063967924037762427

theorem tailTrace_914297 : CollatzResearch.WordTrace tailWord_914297 prefixEnd_914297 417310063967924037762427 := by
  unfold tailWord_914297
  simp only [CollatzResearch.WordTrace]
  refine ⟨33347151168665593341013145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22231434112443728894008763 33347151168665593341013145)
  ·
    refine ⟨25010363376499195005759859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33347151168665593341013145 25010363376499195005759859)
    ·
      refine ⟨37515545064748792508639789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25010363376499195005759859 37515545064748792508639789)
      ·
        refine ⟨14068329399280797190739921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37515545064748792508639789 14068329399280797190739921)
        ·
          refine ⟨10551247049460597893054941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14068329399280797190739921 10551247049460597893054941)
          ·
            refine ⟨3956717643547724209895603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10551247049460597893054941 3956717643547724209895603)
            ·
              refine ⟨5935076465321586314843405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3956717643547724209895603 5935076465321586314843405)
              ·
                refine ⟨2225653674495594868066277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5935076465321586314843405 2225653674495594868066277)
                ·
                  refine ⟨417310063967924037762427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2225653674495594868066277 417310063967924037762427)
                  ·
                    rfl

theorem cell20_914297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_914297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914297 prefixEnd_914297 := by exact prefixLift 914297
  have htrace : WordTrace (prefixWord ++ tailWord_914297) baseStart_914297 baseEnd_914297 := by
    simpa [prefixWord, tailWord_914297, baseEnd_914297] using wordTrace_append hprefix tailTrace_914297
  have hstable : (prefixWord ++ tailWord_914297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914297).length < 2 ^ (prefixWord ++ tailWord_914297).sum := by decide
  have hdescent : baseEnd_914297 < baseStart_914297 := by decide
  rcases family_descends (prefixWord ++ tailWord_914297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914307 : List Nat := [1, 1, 1, 3, 4, 1, 5, 1, 3]
def baseStart_914307 : Nat := 118140960795 + 914307 * 2 ^ 59
def prefixEnd_914307 : Nat := 4983230072969 + 3 ^ 40 * 914307 * 2
def baseEnd_914307 : Nat := 417314628240408447429053

theorem tailTrace_914307 : CollatzResearch.WordTrace tailWord_914307 prefixEnd_914307 417314628240408447429053 := by
  unfold tailWord_914307
  simp only [CollatzResearch.WordTrace]
  refine ⟨33347515898629365048877175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22231677265752910032584783 33347515898629365048877175)
  ·
    refine ⟨50021273847944047573315763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33347515898629365048877175 50021273847944047573315763)
    ·
      refine ⟨75031910771916071359973645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50021273847944047573315763 75031910771916071359973645)
      ·
        refine ⟨28136966539468526759990117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75031910771916071359973645 28136966539468526759990117)
        ·
          refine ⟨5275681226150348767498147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28136966539468526759990117 5275681226150348767498147)
          ·
            refine ⟨7913521839225523151247221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5275681226150348767498147 7913521839225523151247221)
            ·
              refine ⟨741892672427392795429427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7913521839225523151247221 741892672427392795429427)
              ·
                refine ⟨1112839008641089193144141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741892672427392795429427 1112839008641089193144141)
                ·
                  refine ⟨417314628240408447429053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112839008641089193144141 417314628240408447429053)
                  ·
                    rfl

theorem cell20_914307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 3].length) (baseStart_914307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914307 prefixEnd_914307 := by exact prefixLift 914307
  have htrace : WordTrace (prefixWord ++ tailWord_914307) baseStart_914307 baseEnd_914307 := by
    simpa [prefixWord, tailWord_914307, baseEnd_914307] using wordTrace_append hprefix tailTrace_914307
  have hstable : (prefixWord ++ tailWord_914307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914307).length < 2 ^ (prefixWord ++ tailWord_914307).sum := by decide
  have hdescent : baseEnd_914307 < baseStart_914307 := by decide
  rcases family_descends (prefixWord ++ tailWord_914307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914314 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_914314 : Nat := 118140960795 + 914314 * 2 ^ 59
def prefixEnd_914314 : Nat := 4983230072969 + 3 ^ 40 * 914314 * 2
def baseEnd_914314 : Nat := 417317823231147534195691

theorem tailTrace_914314 : CollatzResearch.WordTrace tailWord_914314 prefixEnd_914314 417317823231147534195691 := by
  unfold tailWord_914314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8336942802401001311095499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22231847473069336829587997 8336942802401001311095499)
  ·
    refine ⟨12505414203601501966643249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8336942802401001311095499 12505414203601501966643249)
    ·
      refine ⟨9379060652701126474982437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12505414203601501966643249 9379060652701126474982437)
      ·
        refine ⟨1758573872381461214059207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9379060652701126474982437 1758573872381461214059207)
        ·
          refine ⟨2637860808572191821088811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1758573872381461214059207 2637860808572191821088811)
          ·
            refine ⟨3956791212858287731633217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637860808572191821088811 3956791212858287731633217)
            ·
              refine ⟨2967593409643715798724913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3956791212858287731633217 2967593409643715798724913)
              ·
                refine ⟨2225695057232786849043685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2967593409643715798724913 2225695057232786849043685)
                ·
                  refine ⟨417317823231147534195691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2225695057232786849043685 417317823231147534195691)
                  ·
                    rfl

theorem cell20_914314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_914314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914314 prefixEnd_914314 := by exact prefixLift 914314
  have htrace : WordTrace (prefixWord ++ tailWord_914314) baseStart_914314 baseEnd_914314 := by
    simpa [prefixWord, tailWord_914314, baseEnd_914314] using wordTrace_append hprefix tailTrace_914314
  have hstable : (prefixWord ++ tailWord_914314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914314).length < 2 ^ (prefixWord ++ tailWord_914314).sum := by decide
  have hdescent : baseEnd_914314 < baseStart_914314 := by decide
  rcases family_descends (prefixWord ++ tailWord_914314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914358 : List Nat := [5, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_914358 : Nat := 118140960795 + 914358 * 2 ^ 59
def prefixEnd_914358 : Nat := 4983230072969 + 3 ^ 40 * 914358 * 2
def baseEnd_914358 : Nat := 417337906030078936728845

theorem tailTrace_914358 : CollatzResearch.WordTrace tailWord_914358 prefixEnd_914358 417337906030078936728845 := by
  unfold tailWord_914358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2084336001340287547436483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22232917347629733839322485 2084336001340287547436483)
  ·
    refine ⟨3126504002010431321154725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2084336001340287547436483 3126504002010431321154725)
    ·
      refine ⟨586219500376955872716511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3126504002010431321154725 586219500376955872716511)
      ·
        refine ⟨879329250565433809074767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586219500376955872716511 879329250565433809074767)
        ·
          refine ⟨1318993875848150713612151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879329250565433809074767 1318993875848150713612151)
          ·
            refine ⟨1978490813772226070418227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318993875848150713612151 1978490813772226070418227)
            ·
              refine ⟨2967736220658339105627341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1978490813772226070418227 2967736220658339105627341)
              ·
                refine ⟨1112901082746877164610253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2967736220658339105627341 1112901082746877164610253)
                ·
                  refine ⟨417337906030078936728845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112901082746877164610253 417337906030078936728845)
                  ·
                    rfl

theorem cell20_914358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_914358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914358 prefixEnd_914358 := by exact prefixLift 914358
  have htrace : WordTrace (prefixWord ++ tailWord_914358) baseStart_914358 baseEnd_914358 := by
    simpa [prefixWord, tailWord_914358, baseEnd_914358] using wordTrace_append hprefix tailTrace_914358
  have hstable : (prefixWord ++ tailWord_914358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914358).length < 2 ^ (prefixWord ++ tailWord_914358).sum := by decide
  have hdescent : baseEnd_914358 < baseStart_914358 := by decide
  rcases family_descends (prefixWord ++ tailWord_914358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914380 : List Nat := [2, 2, 1, 4, 1, 1, 1, 8]
def baseStart_914380 : Nat := 118140960795 + 914380 * 2 ^ 59
def prefixEnd_914380 : Nat := 4983230072969 + 3 ^ 40 * 914380 * 2
def baseEnd_914380 : Nat := 139115982476514879331807

theorem tailTrace_914380 : CollatzResearch.WordTrace tailWord_914380 prefixEnd_914380 139115982476514879331807 := by
  unfold tailWord_914380
  simp only [CollatzResearch.WordTrace]
  refine ⟨16675089213682449258142297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22233452284909932344189729 16675089213682449258142297)
  ·
    refine ⟨12506316910261836943606723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16675089213682449258142297 12506316910261836943606723)
    ·
      refine ⟨18759475365392755415410085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12506316910261836943606723 18759475365392755415410085)
      ·
        refine ⟨3517401631011141640389391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18759475365392755415410085 3517401631011141640389391)
        ·
          refine ⟨5276102446516712460584087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3517401631011141640389391 5276102446516712460584087)
          ·
            refine ⟨7914153669775068690876131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5276102446516712460584087 7914153669775068690876131)
            ·
              refine ⟨11871230504662603036314197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7914153669775068690876131 11871230504662603036314197)
              ·
                refine ⟨139115982476514879331807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11871230504662603036314197 139115982476514879331807)
                ·
                  rfl

theorem cell20_914380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_914380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914380 prefixEnd_914380 := by exact prefixLift 914380
  have htrace : WordTrace (prefixWord ++ tailWord_914380) baseStart_914380 baseEnd_914380 := by
    simpa [prefixWord, tailWord_914380, baseEnd_914380] using wordTrace_append hprefix tailTrace_914380
  have hstable : (prefixWord ++ tailWord_914380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914380).length < 2 ^ (prefixWord ++ tailWord_914380).sum := by decide
  have hdescent : baseEnd_914380 < baseStart_914380 := by decide
  rcases family_descends (prefixWord ++ tailWord_914380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914407 : List Nat := [1, 1, 5, 2, 2, 2, 1, 4, 2]
def baseStart_914407 : Nat := 118140960795 + 914407 * 2 ^ 59
def prefixEnd_914407 : Nat := 4983230072969 + 3 ^ 40 * 914407 * 2
def baseEnd_914407 : Nat := 417360270965252544095311

theorem tailTrace_914407 : CollatzResearch.WordTrace tailWord_914407 prefixEnd_914407 417360270965252544095311 := by
  unfold tailWord_914407
  simp only [CollatzResearch.WordTrace]
  refine ⟨33351163198267082127517475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22234108798844721418344983 33351163198267082127517475)
  ·
    refine ⟨50026744797400623191276213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33351163198267082127517475 50026744797400623191276213)
    ·
      refine ⟨4690007324756308424182145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50026744797400623191276213 4690007324756308424182145)
      ·
        refine ⟨3517505493567231318136609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4690007324756308424182145 3517505493567231318136609)
        ·
          refine ⟨2638129120175423488602457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3517505493567231318136609 2638129120175423488602457)
          ·
            refine ⟨1978596840131567616451843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2638129120175423488602457 1978596840131567616451843)
            ·
              refine ⟨2967895260197351424677765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1978596840131567616451843 2967895260197351424677765)
              ·
                refine ⟨556480361287003392127081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2967895260197351424677765 556480361287003392127081)
                ·
                  refine ⟨417360270965252544095311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556480361287003392127081 417360270965252544095311)
                  ·
                    rfl

theorem cell20_914407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 2].length) (baseStart_914407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914407 prefixEnd_914407 := by exact prefixLift 914407
  have htrace : WordTrace (prefixWord ++ tailWord_914407) baseStart_914407 baseEnd_914407 := by
    simpa [prefixWord, tailWord_914407, baseEnd_914407] using wordTrace_append hprefix tailTrace_914407
  have hstable : (prefixWord ++ tailWord_914407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914407).length < 2 ^ (prefixWord ++ tailWord_914407).sum := by decide
  have hdescent : baseEnd_914407 < baseStart_914407 := by decide
  rcases family_descends (prefixWord ++ tailWord_914407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914414 : List Nat := [4, 1, 2, 1, 4, 2, 1, 5]
def baseStart_914414 : Nat := 118140960795 + 914414 * 2 ^ 59
def prefixEnd_914414 : Nat := 4983230072969 + 3 ^ 40 * 914414 * 2
def baseEnd_914414 : Nat := 139121155318663876953983

theorem tailTrace_914414 : CollatzResearch.WordTrace tailWord_914414 prefixEnd_914414 139121155318663876953983 := by
  unfold tailWord_914414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4168927313655215290377787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22234279006161148215348197 4168927313655215290377787)
  ·
    refine ⟨6253390970482822935566681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4168927313655215290377787 6253390970482822935566681)
    ·
      refine ⟨4690043227862117201675011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6253390970482822935566681 4690043227862117201675011)
      ·
        refine ⟨7035064841793175802512517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4690043227862117201675011 7035064841793175802512517)
        ·
          refine ⟨1319074657836220462971097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7035064841793175802512517 1319074657836220462971097)
          ·
            refine ⟨989305993377165347228323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1319074657836220462971097 989305993377165347228323)
            ·
              refine ⟨1483958990065748020842485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989305993377165347228323 1483958990065748020842485)
              ·
                refine ⟨139121155318663876953983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1483958990065748020842485 139121155318663876953983)
                ·
                  rfl

theorem cell20_914414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_914414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914414 prefixEnd_914414 := by exact prefixLift 914414
  have htrace : WordTrace (prefixWord ++ tailWord_914414) baseStart_914414 baseEnd_914414 := by
    simpa [prefixWord, tailWord_914414, baseEnd_914414] using wordTrace_append hprefix tailTrace_914414
  have hstable : (prefixWord ++ tailWord_914414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914414).length < 2 ^ (prefixWord ++ tailWord_914414).sum := by decide
  have hdescent : baseEnd_914414 < baseStart_914414 := by decide
  rcases family_descends (prefixWord ++ tailWord_914414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914456 : List Nat := [2, 1, 2, 3, 2, 3, 7]
def baseStart_914456 : Nat := 118140960795 + 914456 * 2 ^ 59
def prefixEnd_914456 : Nat := 4983230072969 + 3 ^ 40 * 914456 * 2
def baseEnd_914456 : Nat := 46375848433380683495753

theorem tailTrace_914456 : CollatzResearch.WordTrace tailWord_914456 prefixEnd_914456 46375848433380683495753 := by
  unfold tailWord_914456
  simp only [CollatzResearch.WordTrace]
  refine ⟨16676475187544781748025611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22235300250059708997367481 16676475187544781748025611)
  ·
    refine ⟨25014712781317172622038417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16676475187544781748025611 25014712781317172622038417)
    ·
      refine ⟨18761034585987879466528813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25014712781317172622038417 18761034585987879466528813)
      ·
        refine ⟨7035387969745454799948305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18761034585987879466528813 7035387969745454799948305)
        ·
          refine ⟨5276540977309091099961229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7035387969745454799948305 5276540977309091099961229)
          ·
            refine ⟨1978702866490909162485461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5276540977309091099961229 1978702866490909162485461)
            ·
              refine ⟨46375848433380683495753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1978702866490909162485461 46375848433380683495753)
              ·
                rfl

theorem cell20_914456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 7].length) (baseStart_914456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914456 prefixEnd_914456 := by exact prefixLift 914456
  have htrace : WordTrace (prefixWord ++ tailWord_914456) baseStart_914456 baseEnd_914456 := by
    simpa [prefixWord, tailWord_914456, baseEnd_914456] using wordTrace_append hprefix tailTrace_914456
  have hstable : (prefixWord ++ tailWord_914456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914456).length < 2 ^ (prefixWord ++ tailWord_914456).sum := by decide
  have hdescent : baseEnd_914456 < baseStart_914456 := by decide
  rcases family_descends (prefixWord ++ tailWord_914456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914466 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_914466 : Nat := 118140960795 + 914466 * 2 ^ 59
def prefixEnd_914466 : Nat := 4983230072969 + 3 ^ 40 * 914466 * 2
def baseEnd_914466 : Nat := 417387200172910561128403

theorem tailTrace_914466 : CollatzResearch.WordTrace tailWord_914466 prefixEnd_914466 417387200172910561128403 := by
  unfold tailWord_914466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8338328776263333800978813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22235543403368890135943501 8338328776263333800978813)
  ·
    refine ⟨3126873291098750175367055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8338328776263333800978813 3126873291098750175367055)
    ·
      refine ⟨4690309936648125263050583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3126873291098750175367055 4690309936648125263050583)
      ·
        refine ⟨7035464904972187894575875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4690309936648125263050583 7035464904972187894575875)
        ·
          refine ⟨10553197357458281841863813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7035464904972187894575875 10553197357458281841863813)
          ·
            refine ⟨1978724504523427845349465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10553197357458281841863813 1978724504523427845349465)
            ·
              refine ⟨1484043378392570884012099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1978724504523427845349465 1484043378392570884012099)
              ·
                refine ⟨2226065067588856326018149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484043378392570884012099 2226065067588856326018149)
                ·
                  refine ⟨417387200172910561128403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2226065067588856326018149 417387200172910561128403)
                  ·
                    rfl

theorem cell20_914466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_914466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914466 prefixEnd_914466 := by exact prefixLift 914466
  have htrace : WordTrace (prefixWord ++ tailWord_914466) baseStart_914466 baseEnd_914466 := by
    simpa [prefixWord, tailWord_914466, baseEnd_914466] using wordTrace_append hprefix tailTrace_914466
  have hstable : (prefixWord ++ tailWord_914466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914466).length < 2 ^ (prefixWord ++ tailWord_914466).sum := by decide
  have hdescent : baseEnd_914466 < baseStart_914466 := by decide
  rcases family_descends (prefixWord ++ tailWord_914466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914501 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 5]
def baseStart_914501 : Nat := 118140960795 + 914501 * 2 ^ 59
def prefixEnd_914501 : Nat := 4983230072969 + 3 ^ 40 * 914501 * 2
def baseEnd_914501 : Nat := 417403175126605994961593

theorem tailTrace_914501 : CollatzResearch.WordTrace tailWord_914501 prefixEnd_914501 417403175126605994961593 := by
  unfold tailWord_914501
  simp only [CollatzResearch.WordTrace]
  refine ⟨33354591659926536181439357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22236394439951024120959571 33354591659926536181439357)
  ·
    refine ⟨12507971872472451068039759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33354591659926536181439357 12507971872472451068039759)
    ·
      refine ⟨18761957808708676602059639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12507971872472451068039759 18761957808708676602059639)
      ·
        refine ⟨28142936713063014903089459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18761957808708676602059639 28142936713063014903089459)
        ·
          refine ⟨42214405069594522354634189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28142936713063014903089459 42214405069594522354634189)
          ·
            refine ⟨15830401901097945882987821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42214405069594522354634189 15830401901097945882987821)
            ·
              refine ⟨5936400712911729706120433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15830401901097945882987821 5936400712911729706120433)
              ·
                refine ⟨4452300534683797279590325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5936400712911729706120433 4452300534683797279590325)
                ·
                  refine ⟨417403175126605994961593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4452300534683797279590325 417403175126605994961593)
                  ·
                    rfl

theorem cell20_914501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_914501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914501 prefixEnd_914501 := by exact prefixLift 914501
  have htrace : WordTrace (prefixWord ++ tailWord_914501) baseStart_914501 baseEnd_914501 := by
    simpa [prefixWord, tailWord_914501, baseEnd_914501] using wordTrace_append hprefix tailTrace_914501
  have hstable : (prefixWord ++ tailWord_914501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914501).length < 2 ^ (prefixWord ++ tailWord_914501).sum := by decide
  have hdescent : baseEnd_914501 < baseStart_914501 := by decide
  rcases family_descends (prefixWord ++ tailWord_914501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914535 : List Nat := [1, 1, 5, 1, 1, 3, 4, 1, 3]
def baseStart_914535 : Nat := 118140960795 + 914535 * 2 ^ 59
def prefixEnd_914535 : Nat := 4983230072969 + 3 ^ 40 * 914535 * 2
def baseEnd_914535 : Nat := 417418693653052987828121

theorem tailTrace_914535 : CollatzResearch.WordTrace tailWord_914535 prefixEnd_914535 417418693653052987828121 := by
  unfold tailWord_914535
  simp only [CollatzResearch.WordTrace]
  refine ⟨33355831741803359988177059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22237221161202239992118039 33355831741803359988177059)
  ·
    refine ⟨50033747612705039982265589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33355831741803359988177059 50033747612705039982265589)
    ·
      refine ⟨4690663838691097498337399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50033747612705039982265589 4690663838691097498337399)
      ·
        refine ⟨7035995758036646247506099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4690663838691097498337399 7035995758036646247506099)
        ·
          refine ⟨10553993637054969371259149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7035995758036646247506099 10553993637054969371259149)
          ·
            refine ⟨3957747613895613514222181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10553993637054969371259149 3957747613895613514222181)
            ·
              refine ⟨742077677605427533916659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3957747613895613514222181 742077677605427533916659)
              ·
                refine ⟨1113116516408141300874989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742077677605427533916659 1113116516408141300874989)
                ·
                  refine ⟨417418693653052987828121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1113116516408141300874989 417418693653052987828121)
                  ·
                    rfl

theorem cell20_914535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 3].length) (baseStart_914535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914535 prefixEnd_914535 := by exact prefixLift 914535
  have htrace : WordTrace (prefixWord ++ tailWord_914535) baseStart_914535 baseEnd_914535 := by
    simpa [prefixWord, tailWord_914535, baseEnd_914535] using wordTrace_append hprefix tailTrace_914535
  have hstable : (prefixWord ++ tailWord_914535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914535).length < 2 ^ (prefixWord ++ tailWord_914535).sum := by decide
  have hdescent : baseEnd_914535 < baseStart_914535 := by decide
  rcases family_descends (prefixWord ++ tailWord_914535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914615 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 5]
def baseStart_914615 : Nat := 118140960795 + 914615 * 2 ^ 59
def prefixEnd_914615 : Nat := 4983230072969 + 3 ^ 40 * 914615 * 2
def baseEnd_914615 : Nat := 417455207832928265161127

theorem tailTrace_914615 : CollatzResearch.WordTrace tailWord_914615 prefixEnd_914615 417455207832928265161127 := by
  unfold tailWord_914615
  simp only [CollatzResearch.WordTrace]
  refine ⟨33358749581513533651089299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22239166387675689100726199 33358749581513533651089299)
  ·
    refine ⟨50038124372270300476633949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33358749581513533651089299 50038124372270300476633949)
    ·
      refine ⟨18764296639601362678737731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50038124372270300476633949 18764296639601362678737731)
      ·
        refine ⟨28146444959402044018106597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18764296639601362678737731 28146444959402044018106597)
        ·
          refine ⟨5277458429887883253394987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28146444959402044018106597 5277458429887883253394987)
          ·
            refine ⟨7916187644831824880092481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5277458429887883253394987 7916187644831824880092481)
            ·
              refine ⟨5937140733623868660069361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7916187644831824880092481 5937140733623868660069361)
              ·
                refine ⟨4452855550217901495052021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5937140733623868660069361 4452855550217901495052021)
                ·
                  refine ⟨417455207832928265161127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4452855550217901495052021 417455207832928265161127)
                  ·
                    rfl

theorem cell20_914615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_914615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914615 prefixEnd_914615 := by exact prefixLift 914615
  have htrace : WordTrace (prefixWord ++ tailWord_914615) baseStart_914615 baseEnd_914615 := by
    simpa [prefixWord, tailWord_914615, baseEnd_914615] using wordTrace_append hprefix tailTrace_914615
  have hstable : (prefixWord ++ tailWord_914615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914615).length < 2 ^ (prefixWord ++ tailWord_914615).sum := by decide
  have hdescent : baseEnd_914615 < baseStart_914615 := by decide
  rcases family_descends (prefixWord ++ tailWord_914615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914625 : List Nat := [1, 2, 6, 1, 1, 2, 7]
def baseStart_914625 : Nat := 118140960795 + 914625 * 2 ^ 59
def prefixEnd_914625 : Nat := 4983230072969 + 3 ^ 40 * 914625 * 2
def baseEnd_914625 : Nat := 46384419122823630536417

theorem tailTrace_914625 : CollatzResearch.WordTrace tailWord_914625 prefixEnd_914625 46384419122823630536417 := by
  unfold tailWord_914625
  simp only [CollatzResearch.WordTrace]
  refine ⟨33359114311477305358953329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22239409540984870239302219 33359114311477305358953329)
  ·
    refine ⟨25019335733607979019214997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33359114311477305358953329 25019335733607979019214997)
    ·
      refine ⟨1172781362512874016525703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25019335733607979019214997 1172781362512874016525703)
      ·
        refine ⟨1759172043769311024788555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1172781362512874016525703 1759172043769311024788555)
        ·
          refine ⟨2638758065653966537182833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1759172043769311024788555 2638758065653966537182833)
          ·
            refine ⟨1979068549240474902887125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2638758065653966537182833 1979068549240474902887125)
            ·
              refine ⟨46384419122823630536417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1979068549240474902887125 46384419122823630536417)
              ·
                rfl

theorem cell20_914625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 7].length) (baseStart_914625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914625 prefixEnd_914625 := by exact prefixLift 914625
  have htrace : WordTrace (prefixWord ++ tailWord_914625) baseStart_914625 baseEnd_914625 := by
    simpa [prefixWord, tailWord_914625, baseEnd_914625] using wordTrace_append hprefix tailTrace_914625
  have hstable : (prefixWord ++ tailWord_914625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914625).length < 2 ^ (prefixWord ++ tailWord_914625).sum := by decide
  have hdescent : baseEnd_914625 < baseStart_914625 := by decide
  rcases family_descends (prefixWord ++ tailWord_914625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914628 : List Nat := [2, 3, 3, 1, 3, 2, 1, 2, 3]
def baseStart_914628 : Nat := 118140960795 + 914628 * 2 ^ 59
def prefixEnd_914628 : Nat := 4983230072969 + 3 ^ 40 * 914628 * 2
def baseEnd_914628 : Nat := 417461141387157997727741

theorem tailTrace_914628 : CollatzResearch.WordTrace tailWord_914628 prefixEnd_914628 417461141387157997727741 := by
  unfold tailWord_914628
  simp only [CollatzResearch.WordTrace]
  refine ⟨16679611865233218435656269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22239482486977624580875025 16679611865233218435656269)
  ·
    refine ⟨6254854449462456913371101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16679611865233218435656269 6254854449462456913371101)
    ·
      refine ⟨2345570418548421342514163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6254854449462456913371101 2345570418548421342514163)
      ·
        refine ⟨3518355627822632013771245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2345570418548421342514163 3518355627822632013771245)
        ·
          refine ⟨1319383360433487005164217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3518355627822632013771245 1319383360433487005164217)
          ·
            refine ⟨989537520325115253873163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1319383360433487005164217 989537520325115253873163)
            ·
              refine ⟨1484306280487672880809745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989537520325115253873163 1484306280487672880809745)
              ·
                refine ⟨1113229710365754660607309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1484306280487672880809745 1113229710365754660607309)
                ·
                  refine ⟨417461141387157997727741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1113229710365754660607309 417461141387157997727741)
                  ·
                    rfl

theorem cell20_914628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_914628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914628 prefixEnd_914628 := by exact prefixLift 914628
  have htrace : WordTrace (prefixWord ++ tailWord_914628) baseStart_914628 baseEnd_914628 := by
    simpa [prefixWord, tailWord_914628, baseEnd_914628] using wordTrace_append hprefix tailTrace_914628
  have hstable : (prefixWord ++ tailWord_914628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914628).length < 2 ^ (prefixWord ++ tailWord_914628).sum := by decide
  have hdescent : baseEnd_914628 < baseStart_914628 := by decide
  rcases family_descends (prefixWord ++ tailWord_914628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914632 : List Nat := [2, 1, 3, 1, 2, 1, 5, 2, 3]
def baseStart_914632 : Nat := 118140960795 + 914632 * 2 ^ 59
def prefixEnd_914632 : Nat := 4983230072969 + 3 ^ 40 * 914632 * 2
def baseEnd_914632 : Nat := 417462967096151761594391

theorem tailTrace_914632 : CollatzResearch.WordTrace tailWord_914632 prefixEnd_914632 417462967096151761594391 := by
  unfold tailWord_914632
  simp only [CollatzResearch.WordTrace]
  refine ⟨16679684811225972777229075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22239579748301297036305433 16679684811225972777229075)
  ·
    refine ⟨25019527216838959165843613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16679684811225972777229075 25019527216838959165843613)
    ·
      refine ⟨9382322706314609687191355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25019527216838959165843613 9382322706314609687191355)
      ·
        refine ⟨14073484059471914530787033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9382322706314609687191355 14073484059471914530787033)
        ·
          refine ⟨10555113044603935898090275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14073484059471914530787033 10555113044603935898090275)
          ·
            refine ⟨15832669566905903847135413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10555113044603935898090275 15832669566905903847135413)
            ·
              refine ⟨1484312771897428485668945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15832669566905903847135413 1484312771897428485668945)
              ·
                refine ⟨1113234578923071364251709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1484312771897428485668945 1113234578923071364251709)
                ·
                  refine ⟨417462967096151761594391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1113234578923071364251709 417462967096151761594391)
                  ·
                    rfl

theorem cell20_914632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_914632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914632 prefixEnd_914632 := by exact prefixLift 914632
  have htrace : WordTrace (prefixWord ++ tailWord_914632) baseStart_914632 baseEnd_914632 := by
    simpa [prefixWord, tailWord_914632, baseEnd_914632] using wordTrace_append hprefix tailTrace_914632
  have hstable : (prefixWord ++ tailWord_914632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914632).length < 2 ^ (prefixWord ++ tailWord_914632).sum := by decide
  have hdescent : baseEnd_914632 < baseStart_914632 := by decide
  rcases family_descends (prefixWord ++ tailWord_914632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914663 : List Nat := [1, 1, 5, 3, 2, 1, 1, 6]
def baseStart_914663 : Nat := 118140960795 + 914663 * 2 ^ 59
def prefixEnd_914663 : Nat := 4983230072969 + 3 ^ 40 * 914663 * 2
def baseEnd_914663 : Nat := 139159038780284477186977

theorem tailTrace_914663 : CollatzResearch.WordTrace tailWord_914663 prefixEnd_914663 139159038780284477186977 := by
  unfold tailWord_914663
  simp only [CollatzResearch.WordTrace]
  refine ⟨33360500285339637848836643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22240333523559758565891095 33360500285339637848836643)
  ·
    refine ⟨50040750428009456773254965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33360500285339637848836643 50040750428009456773254965)
    ·
      refine ⟨4691320352625886572492653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50040750428009456773254965 4691320352625886572492653)
      ·
        refine ⟨1759245132234707464684745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4691320352625886572492653 1759245132234707464684745)
        ·
          refine ⟨1319433849176030598513559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1759245132234707464684745 1319433849176030598513559)
          ·
            refine ⟨1979150773764045897770339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319433849176030598513559 1979150773764045897770339)
            ·
              refine ⟨2968726160646068846655509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1979150773764045897770339 2968726160646068846655509)
              ·
                refine ⟨139159038780284477186977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2968726160646068846655509 139159038780284477186977)
                ·
                  rfl

theorem cell20_914663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 6].length) (baseStart_914663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914663 prefixEnd_914663 := by exact prefixLift 914663
  have htrace : WordTrace (prefixWord ++ tailWord_914663) baseStart_914663 baseEnd_914663 := by
    simpa [prefixWord, tailWord_914663, baseEnd_914663] using wordTrace_append hprefix tailTrace_914663
  have hstable : (prefixWord ++ tailWord_914663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914663).length < 2 ^ (prefixWord ++ tailWord_914663).sum := by decide
  have hdescent : baseEnd_914663 < baseStart_914663 := by decide
  rcases family_descends (prefixWord ++ tailWord_914663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914676 : List Nat := [2, 6, 1, 2, 2, 1, 6]
def baseStart_914676 : Nat := 118140960795 + 914676 * 2 ^ 59
def prefixEnd_914676 : Nat := 4983230072969 + 3 ^ 40 * 914676 * 2
def baseEnd_914676 : Nat := 46387005543898129347505

theorem tailTrace_914676 : CollatzResearch.WordTrace tailWord_914676 prefixEnd_914676 46387005543898129347505 := by
  unfold tailWord_914676
  simp only [CollatzResearch.WordTrace]
  refine ⟨16680487217146270534529941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22240649622861694046039921 16680487217146270534529941)
  ·
    refine ⟨781897838303731431306091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16680487217146270534529941 781897838303731431306091)
    ·
      refine ⟨1172846757455597146959137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 781897838303731431306091 1172846757455597146959137)
      ·
        refine ⟨879635068091697860219353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1172846757455597146959137 879635068091697860219353)
        ·
          refine ⟨659726301068773395164515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 879635068091697860219353 659726301068773395164515)
          ·
            refine ⟨989589451603160092746773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659726301068773395164515 989589451603160092746773)
            ·
              refine ⟨46387005543898129347505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 989589451603160092746773 46387005543898129347505)
              ·
                rfl

theorem cell20_914676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 6].length) (baseStart_914676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914676 prefixEnd_914676 := by exact prefixLift 914676
  have htrace : WordTrace (prefixWord ++ tailWord_914676) baseStart_914676 baseEnd_914676 := by
    simpa [prefixWord, tailWord_914676, baseEnd_914676] using wordTrace_append hprefix tailTrace_914676
  have hstable : (prefixWord ++ tailWord_914676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914676).length < 2 ^ (prefixWord ++ tailWord_914676).sum := by decide
  have hdescent : baseEnd_914676 < baseStart_914676 := by decide
  rcases family_descends (prefixWord ++ tailWord_914676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914690 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 4]
def baseStart_914690 : Nat := 118140960795 + 914690 * 2 ^ 59
def prefixEnd_914690 : Nat := 4983230072969 + 3 ^ 40 * 914690 * 2
def baseEnd_914690 : Nat := 417489439876561337660821

theorem tailTrace_914690 : CollatzResearch.WordTrace tailWord_914690 prefixEnd_914690 417489439876561337660821 := by
  unfold tailWord_914690
  simp only [CollatzResearch.WordTrace]
  refine ⟨8340371264060455365017381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22240990037494547640046349 8340371264060455365017381)
  ·
    refine ⟨1563819612011335380940759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8340371264060455365017381 1563819612011335380940759)
    ·
      refine ⟨2345729418017003071411139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1563819612011335380940759 2345729418017003071411139)
      ·
        refine ⟨3518594127025504607116709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2345729418017003071411139 3518594127025504607116709)
        ·
          refine ⟨659736398817282113834383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3518594127025504607116709 659736398817282113834383)
          ·
            refine ⟨989604598225923170751575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659736398817282113834383 989604598225923170751575)
            ·
              refine ⟨1484406897338884756127363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989604598225923170751575 1484406897338884756127363)
              ·
                refine ⟨2226610346008327134191045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484406897338884756127363 2226610346008327134191045)
                ·
                  refine ⟨417489439876561337660821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2226610346008327134191045 417489439876561337660821)
                  ·
                    rfl

theorem cell20_914690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_914690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914690 prefixEnd_914690 := by exact prefixLift 914690
  have htrace : WordTrace (prefixWord ++ tailWord_914690) baseStart_914690 baseEnd_914690 := by
    simpa [prefixWord, tailWord_914690, baseEnd_914690] using wordTrace_append hprefix tailTrace_914690
  have hstable : (prefixWord ++ tailWord_914690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914690).length < 2 ^ (prefixWord ++ tailWord_914690).sum := by decide
  have hdescent : baseEnd_914690 < baseStart_914690 := by decide
  rcases family_descends (prefixWord ++ tailWord_914690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914691 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 5]
def baseStart_914691 : Nat := 118140960795 + 914691 * 2 ^ 59
def prefixEnd_914691 : Nat := 4983230072969 + 3 ^ 40 * 914691 * 2
def baseEnd_914691 : Nat := 417489896303809778627483

theorem tailTrace_914691 : CollatzResearch.WordTrace tailWord_914691 prefixEnd_914691 417489896303809778627483 := by
  unfold tailWord_914691
  simp only [CollatzResearch.WordTrace]
  refine ⟨33361521529238198630855927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22241014352825465753903951 33361521529238198630855927)
  ·
    refine ⟨50042282293857297946283891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33361521529238198630855927 50042282293857297946283891)
    ·
      refine ⟨75063423440785946919425837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50042282293857297946283891 75063423440785946919425837)
      ·
        refine ⟨28148783790294730094784689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75063423440785946919425837 28148783790294730094784689)
        ·
          refine ⟨21111587842721047571088517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28148783790294730094784689 21111587842721047571088517)
          ·
            refine ⟨3958422720510196419579097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21111587842721047571088517 3958422720510196419579097)
            ·
              refine ⟨2968817040382647314684323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3958422720510196419579097 2968817040382647314684323)
              ·
                refine ⟨4453225560573970972026485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2968817040382647314684323 4453225560573970972026485)
                ·
                  refine ⟨417489896303809778627483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4453225560573970972026485 417489896303809778627483)
                  ·
                    rfl

theorem cell20_914691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_914691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914691 prefixEnd_914691 := by exact prefixLift 914691
  have htrace : WordTrace (prefixWord ++ tailWord_914691) baseStart_914691 baseEnd_914691 := by
    simpa [prefixWord, tailWord_914691, baseEnd_914691] using wordTrace_append hprefix tailTrace_914691
  have hstable : (prefixWord ++ tailWord_914691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914691).length < 2 ^ (prefixWord ++ tailWord_914691).sum := by decide
  have hdescent : baseEnd_914691 < baseStart_914691 := by decide
  rcases family_descends (prefixWord ++ tailWord_914691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914745 : List Nat := [1, 2, 1, 6, 3, 1, 2, 2, 2]
def baseStart_914745 : Nat := 118140960795 + 914745 * 2 ^ 59
def prefixEnd_914745 : Nat := 4983230072969 + 3 ^ 40 * 914745 * 2
def baseEnd_914745 : Nat := 417514543375225590827263

theorem tailTrace_914745 : CollatzResearch.WordTrace tailWord_914745 prefixEnd_914745 417514543375225590827263 := by
  unfold tailWord_914745
  simp only [CollatzResearch.WordTrace]
  refine ⟨33363491071042565853321689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22242327380695043902214459 33363491071042565853321689)
  ·
    refine ⟨25022618303281924389991267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33363491071042565853321689 25022618303281924389991267)
    ·
      refine ⟨37533927454922886584986901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25022618303281924389991267 37533927454922886584986901)
      ·
        refine ⟨1759402849449510308671261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37533927454922886584986901 1759402849449510308671261)
        ·
          refine ⟨659776068543566365751723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1759402849449510308671261 659776068543566365751723)
          ·
            refine ⟨989664102815349548627585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659776068543566365751723 989664102815349548627585)
            ·
              refine ⟨742248077111512161470689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 989664102815349548627585 742248077111512161470689)
              ·
                refine ⟨556686057833634121103017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 742248077111512161470689 556686057833634121103017)
                ·
                  refine ⟨417514543375225590827263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556686057833634121103017 417514543375225590827263)
                  ·
                    rfl

theorem cell20_914745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 2].length) (baseStart_914745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914745 prefixEnd_914745 := by exact prefixLift 914745
  have htrace : WordTrace (prefixWord ++ tailWord_914745) baseStart_914745 baseEnd_914745 := by
    simpa [prefixWord, tailWord_914745, baseEnd_914745] using wordTrace_append hprefix tailTrace_914745
  have hstable : (prefixWord ++ tailWord_914745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914745).length < 2 ^ (prefixWord ++ tailWord_914745).sum := by decide
  have hdescent : baseEnd_914745 < baseStart_914745 := by decide
  rcases family_descends (prefixWord ++ tailWord_914745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914746 : List Nat := [3, 1, 1, 1, 4, 1, 4, 2, 3]
def baseStart_914746 : Nat := 118140960795 + 914746 * 2 ^ 59
def prefixEnd_914746 : Nat := 4983230072969 + 3 ^ 40 * 914746 * 2
def baseEnd_914746 : Nat := 417514999802474031793925

theorem tailTrace_914746 : CollatzResearch.WordTrace tailWord_914746 prefixEnd_914746 417514999802474031793925 := by
  unfold tailWord_914746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8340881886009735756027023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22242351696025962016072061 8340881886009735756027023)
  ·
    refine ⟨12511322829014603634040535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8340881886009735756027023 12511322829014603634040535)
    ·
      refine ⟨18766984243521905451060803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12511322829014603634040535 18766984243521905451060803)
      ·
        refine ⟨28150476365282858176591205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18766984243521905451060803 28150476365282858176591205)
        ·
          refine ⟨5278214318490535908110851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28150476365282858176591205 5278214318490535908110851)
          ·
            refine ⟨7917321477735803862166277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5278214318490535908110851 7917321477735803862166277)
            ·
              refine ⟨1484497777075463224156177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7917321477735803862166277 1484497777075463224156177)
              ·
                refine ⟨1113373332806597418117133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1484497777075463224156177 1113373332806597418117133)
                ·
                  refine ⟨417514999802474031793925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1113373332806597418117133 417514999802474031793925)
                  ·
                    rfl

theorem cell20_914746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_914746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914746 prefixEnd_914746 := by exact prefixLift 914746
  have htrace : WordTrace (prefixWord ++ tailWord_914746) baseStart_914746 baseEnd_914746 := by
    simpa [prefixWord, tailWord_914746, baseEnd_914746] using wordTrace_append hprefix tailTrace_914746
  have hstable : (prefixWord ++ tailWord_914746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914746).length < 2 ^ (prefixWord ++ tailWord_914746).sum := by decide
  have hdescent : baseEnd_914746 < baseStart_914746 := by decide
  rcases family_descends (prefixWord ++ tailWord_914746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914756 : List Nat := [2, 3, 4, 1, 1, 3, 1, 5]
def baseStart_914756 : Nat := 118140960795 + 914756 * 2 ^ 59
def prefixEnd_914756 : Nat := 4983230072969 + 3 ^ 40 * 914756 * 2
def baseEnd_914756 : Nat := 139173188024986147153517

theorem tailTrace_914756 : CollatzResearch.WordTrace tailWord_914756 prefixEnd_914756 139173188024986147153517 := by
  unfold tailWord_914756
  simp only [CollatzResearch.WordTrace]
  refine ⟨16681946137001357365986061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22242594849335143154648081 16681946137001357365986061)
  ·
    refine ⟨6255729801375509012244773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16681946137001357365986061 6255729801375509012244773)
    ·
      refine ⟨1172949337757907939795895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6255729801375509012244773 1172949337757907939795895)
      ·
        refine ⟨1759424006636861909693843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1172949337757907939795895 1759424006636861909693843)
        ·
          refine ⟨2639136009955292864540765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1759424006636861909693843 2639136009955292864540765)
          ·
            refine ⟨989676003733234824202787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2639136009955292864540765 989676003733234824202787)
            ·
              refine ⟨1484514005599852236304181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989676003733234824202787 1484514005599852236304181)
              ·
                refine ⟨139173188024986147153517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1484514005599852236304181 139173188024986147153517)
                ·
                  rfl

theorem cell20_914756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_914756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914756 prefixEnd_914756 := by exact prefixLift 914756
  have htrace : WordTrace (prefixWord ++ tailWord_914756) baseStart_914756 baseEnd_914756 := by
    simpa [prefixWord, tailWord_914756, baseEnd_914756] using wordTrace_append hprefix tailTrace_914756
  have hstable : (prefixWord ++ tailWord_914756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914756).length < 2 ^ (prefixWord ++ tailWord_914756).sum := by decide
  have hdescent : baseEnd_914756 < baseStart_914756 := by decide
  rcases family_descends (prefixWord ++ tailWord_914756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914867 : List Nat := [1, 1, 1, 2, 3, 1, 1, 8, 2]
def baseStart_914867 : Nat := 118140960795 + 914867 * 2 ^ 59
def prefixEnd_914867 : Nat := 4983230072969 + 3 ^ 40 * 914867 * 2
def baseEnd_914867 : Nat := 417570227499535388760097

theorem tailTrace_914867 : CollatzResearch.WordTrace tailWord_914867 prefixEnd_914867 417570227499535388760097 := by
  unfold tailWord_914867
  simp only [CollatzResearch.WordTrace]
  refine ⟨33367940776600580689262855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22245293851067053792841903 33367940776600580689262855)
  ·
    refine ⟨50051911164900871033894283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33367940776600580689262855 50051911164900871033894283)
    ·
      refine ⟨75077866747351306550841425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50051911164900871033894283 75077866747351306550841425)
      ·
        refine ⟨56308400060513479913131069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75077866747351306550841425 56308400060513479913131069)
        ·
          refine ⟨21115650022692554967424151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56308400060513479913131069 21115650022692554967424151)
          ·
            refine ⟨31673475034038832451136227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21115650022692554967424151 31673475034038832451136227)
            ·
              refine ⟨47510212551058248676704341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31673475034038832451136227 47510212551058248676704341)
              ·
                refine ⟨556760303332713851680129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 47510212551058248676704341 556760303332713851680129)
                ·
                  refine ⟨417570227499535388760097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556760303332713851680129 417570227499535388760097)
                  ·
                    rfl

theorem cell20_914867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 2].length) (baseStart_914867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914867 prefixEnd_914867 := by exact prefixLift 914867
  have htrace : WordTrace (prefixWord ++ tailWord_914867) baseStart_914867 baseEnd_914867 := by
    simpa [prefixWord, tailWord_914867, baseEnd_914867] using wordTrace_append hprefix tailTrace_914867
  have hstable : (prefixWord ++ tailWord_914867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914867).length < 2 ^ (prefixWord ++ tailWord_914867).sum := by decide
  have hdescent : baseEnd_914867 < baseStart_914867 := by decide
  rcases family_descends (prefixWord ++ tailWord_914867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914888 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 6]
def baseStart_914888 : Nat := 118140960795 + 914888 * 2 ^ 59
def prefixEnd_914888 : Nat := 4983230072969 + 3 ^ 40 * 914888 * 2
def baseEnd_914888 : Nat := 417579812471752649060011

theorem tailTrace_914888 : CollatzResearch.WordTrace tailWord_914888 prefixEnd_914888 417579812471752649060011 := by
  unfold tailWord_914888
  simp only [CollatzResearch.WordTrace]
  refine ⟨16684353354762250637888659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22245804473016334183851545 16684353354762250637888659)
  ·
    refine ⟨25026530032143375956832989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16684353354762250637888659 25026530032143375956832989)
    ·
      refine ⟨9384948762053765983812371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25026530032143375956832989 9384948762053765983812371)
      ·
        refine ⟨14077423143080648975718557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9384948762053765983812371 14077423143080648975718557)
        ·
          refine ⟨5279033678655243365894459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14077423143080648975718557 5279033678655243365894459)
          ·
            refine ⟨7918550517982865048841689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5279033678655243365894459 7918550517982865048841689)
            ·
              refine ⟨5938912888487148786631267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7918550517982865048841689 5938912888487148786631267)
              ·
                refine ⟨8908369332730723179946901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5938912888487148786631267 8908369332730723179946901)
                ·
                  refine ⟨417579812471752649060011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8908369332730723179946901 417579812471752649060011)
                  ·
                    rfl

theorem cell20_914888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_914888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914888 prefixEnd_914888 := by exact prefixLift 914888
  have htrace : WordTrace (prefixWord ++ tailWord_914888) baseStart_914888 baseEnd_914888 := by
    simpa [prefixWord, tailWord_914888, baseEnd_914888] using wordTrace_append hprefix tailTrace_914888
  have hstable : (prefixWord ++ tailWord_914888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914888).length < 2 ^ (prefixWord ++ tailWord_914888).sum := by decide
  have hdescent : baseEnd_914888 < baseStart_914888 := by decide
  rcases family_descends (prefixWord ++ tailWord_914888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914895 : List Nat := [1, 1, 2, 1, 1, 4, 4, 6]
def baseStart_914895 : Nat := 118140960795 + 914895 * 2 ^ 59
def prefixEnd_914895 : Nat := 4983230072969 + 3 ^ 40 * 914895 * 2
def baseEnd_914895 : Nat := 139194335820830578608883

theorem tailTrace_914895 : CollatzResearch.WordTrace tailWord_914895 prefixEnd_914895 139194335820830578608883 := by
  unfold tailWord_914895
  simp only [CollatzResearch.WordTrace]
  refine ⟨33368962020499141471282139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22245974680332760980854759 33368962020499141471282139)
  ·
    refine ⟨50053443030748712206923209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33368962020499141471282139 50053443030748712206923209)
    ·
      refine ⟨37540082273061534155192407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50053443030748712206923209 37540082273061534155192407)
      ·
        refine ⟨56310123409592301232788611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37540082273061534155192407 56310123409592301232788611)
        ·
          refine ⟨84465185114388451849182917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56310123409592301232788611 84465185114388451849182917)
          ·
            refine ⟨15837222208947834721721797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84465185114388451849182917 15837222208947834721721797)
            ·
              refine ⟨2969479164177719010322837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15837222208947834721721797 2969479164177719010322837)
              ·
                refine ⟨139194335820830578608883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2969479164177719010322837 139194335820830578608883)
                ·
                  rfl

theorem cell20_914895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 6].length) (baseStart_914895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914895 prefixEnd_914895 := by exact prefixLift 914895
  have htrace : WordTrace (prefixWord ++ tailWord_914895) baseStart_914895 baseEnd_914895 := by
    simpa [prefixWord, tailWord_914895, baseEnd_914895] using wordTrace_append hprefix tailTrace_914895
  have hstable : (prefixWord ++ tailWord_914895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914895).length < 2 ^ (prefixWord ++ tailWord_914895).sum := by decide
  have hdescent : baseEnd_914895 < baseStart_914895 := by decide
  rcases family_descends (prefixWord ++ tailWord_914895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914946 : List Nat := [3, 4, 1, 2, 1, 2, 3, 4]
def baseStart_914946 : Nat := 118140960795 + 914946 * 2 ^ 59
def prefixEnd_914946 : Nat := 4983230072969 + 3 ^ 40 * 914946 * 2
def baseEnd_914946 : Nat := 139202095084054075042147

theorem tailTrace_914946 : CollatzResearch.WordTrace tailWord_914946 prefixEnd_914946 139202095084054075042147 := by
  unfold tailWord_914946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8342705535828594295347173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22247214762209584787592461 8342705535828594295347173)
  ·
    refine ⟨1564257287967861430377595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8342705535828594295347173 1564257287967861430377595)
    ·
      refine ⟨2346385931951792145566393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1564257287967861430377595 2346385931951792145566393)
      ·
        refine ⟨1759789448963844109174795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2346385931951792145566393 1759789448963844109174795)
        ·
          refine ⟨2639684173445766163762193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1759789448963844109174795 2639684173445766163762193)
          ·
            refine ⟨1979763130084324622821645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2639684173445766163762193 1979763130084324622821645)
            ·
              refine ⟨742411173781621733558117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1979763130084324622821645 742411173781621733558117)
              ·
                refine ⟨139202095084054075042147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 742411173781621733558117 139202095084054075042147)
                ·
                  rfl

theorem cell20_914946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_914946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_914946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_914946 prefixEnd_914946 := by exact prefixLift 914946
  have htrace : WordTrace (prefixWord ++ tailWord_914946) baseStart_914946 baseEnd_914946 := by
    simpa [prefixWord, tailWord_914946, baseEnd_914946] using wordTrace_append hprefix tailTrace_914946
  have hstable : (prefixWord ++ tailWord_914946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914946).length < 2 ^ (prefixWord ++ tailWord_914946).sum := by decide
  have hdescent : baseEnd_914946 < baseStart_914946 := by decide
  rcases family_descends (prefixWord ++ tailWord_914946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915002 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_915002 : Nat := 118140960795 + 915002 * 2 ^ 59
def prefixEnd_915002 : Nat := 4983230072969 + 3 ^ 40 * 915002 * 2
def baseEnd_915002 : Nat := 417631845178074919259545

theorem tailTrace_915002 : CollatzResearch.WordTrace tailWord_915002 prefixEnd_915002 417631845178074919259545 := by
  unfold tailWord_915002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8343216157777874686356815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22248576420740999163618173 8343216157777874686356815)
  ·
    refine ⟨12514824236666812029535223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8343216157777874686356815 12514824236666812029535223)
    ·
      refine ⟨18772236355000218044302835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12514824236666812029535223 18772236355000218044302835)
      ·
        refine ⟨28158354532500327066454253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18772236355000218044302835 28158354532500327066454253)
        ·
          refine ⟨10559382949687622649920345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28158354532500327066454253 10559382949687622649920345)
          ·
            refine ⟨7919537212265716987440259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10559382949687622649920345 7919537212265716987440259)
            ·
              refine ⟨11879305818398575481160389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7919537212265716987440259 11879305818398575481160389)
              ·
                refine ⟨2227369840949732902717573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11879305818398575481160389 2227369840949732902717573)
                ·
                  refine ⟨417631845178074919259545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2227369840949732902717573 417631845178074919259545)
                  ·
                    rfl

theorem cell20_915002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_915002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915002 prefixEnd_915002 := by exact prefixLift 915002
  have htrace : WordTrace (prefixWord ++ tailWord_915002) baseStart_915002 baseEnd_915002 := by
    simpa [prefixWord, tailWord_915002, baseEnd_915002] using wordTrace_append hprefix tailTrace_915002
  have hstable : (prefixWord ++ tailWord_915002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915002).length < 2 ^ (prefixWord ++ tailWord_915002).sum := by decide
  have hdescent : baseEnd_915002 < baseStart_915002 := by decide
  rcases family_descends (prefixWord ++ tailWord_915002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915015 : List Nat := [1, 1, 4, 1, 5, 2, 1, 3, 2]
def baseStart_915015 : Nat := 118140960795 + 915015 * 2 ^ 59
def prefixEnd_915015 : Nat := 4983230072969 + 3 ^ 40 * 915015 * 2
def baseEnd_915015 : Nat := 417637778732304651826159

theorem tailTrace_915015 : CollatzResearch.WordTrace tailWord_915015 prefixEnd_915015 417637778732304651826159 := by
  unfold tailWord_915015
  simp only [CollatzResearch.WordTrace]
  refine ⟨33373338780064401965650499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22248892520042934643766999 33373338780064401965650499)
  ·
    refine ⟨50060008170096602948475749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33373338780064401965650499 50060008170096602948475749)
    ·
      refine ⟨9386251531893113052839203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50060008170096602948475749 9386251531893113052839203)
      ·
        refine ⟨14079377297839669579258805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9386251531893113052839203 14079377297839669579258805)
        ·
          refine ⟨1319941621672469023055513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14079377297839669579258805 1319941621672469023055513)
          ·
            refine ⟨989956216254351767291635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1319941621672469023055513 989956216254351767291635)
            ·
              refine ⟨1484934324381527650937453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989956216254351767291635 1484934324381527650937453)
              ·
                refine ⟨556850371643072869101545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1484934324381527650937453 556850371643072869101545)
                ·
                  refine ⟨417637778732304651826159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556850371643072869101545 417637778732304651826159)
                  ·
                    rfl

theorem cell20_915015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 2].length) (baseStart_915015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915015 prefixEnd_915015 := by exact prefixLift 915015
  have htrace : WordTrace (prefixWord ++ tailWord_915015) baseStart_915015 baseEnd_915015 := by
    simpa [prefixWord, tailWord_915015, baseEnd_915015] using wordTrace_append hprefix tailTrace_915015
  have hstable : (prefixWord ++ tailWord_915015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915015).length < 2 ^ (prefixWord ++ tailWord_915015).sum := by decide
  have hdescent : baseEnd_915015 < baseStart_915015 := by decide
  rcases family_descends (prefixWord ++ tailWord_915015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915026 : List Nat := [3, 2, 2, 1, 2, 4, 6]
def baseStart_915026 : Nat := 118140960795 + 915026 * 2 ^ 59
def prefixEnd_915026 : Nat := 4983230072969 + 3 ^ 40 * 915026 * 2
def baseEnd_915026 : Nat := 46404755492448611384383

theorem tailTrace_915026 : CollatzResearch.WordTrace tailWord_915026 prefixEnd_915026 46404755492448611384383 := by
  unfold tailWord_915026
  simp only [CollatzResearch.WordTrace]
  refine ⟨8343434995756137711075233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22249159988683033896200621 8343434995756137711075233)
  ·
    refine ⟨6257576246817103283306425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8343434995756137711075233 6257576246817103283306425)
    ·
      refine ⟨4693182185112827462479819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6257576246817103283306425 4693182185112827462479819)
      ·
        refine ⟨7039773277669241193719729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4693182185112827462479819 7039773277669241193719729)
        ·
          refine ⟨5279829958251930895289797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7039773277669241193719729 5279829958251930895289797)
          ·
            refine ⟨989968117172237042866837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5279829958251930895289797 989968117172237042866837)
            ·
              refine ⟨46404755492448611384383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 989968117172237042866837 46404755492448611384383)
              ·
                rfl

theorem cell20_915026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 6].length) (baseStart_915026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915026 prefixEnd_915026 := by exact prefixLift 915026
  have htrace : WordTrace (prefixWord ++ tailWord_915026) baseStart_915026 baseEnd_915026 := by
    simpa [prefixWord, tailWord_915026, baseEnd_915026] using wordTrace_append hprefix tailTrace_915026
  have hstable : (prefixWord ++ tailWord_915026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915026).length < 2 ^ (prefixWord ++ tailWord_915026).sum := by decide
  have hdescent : baseEnd_915026 < baseStart_915026 := by decide
  rcases family_descends (prefixWord ++ tailWord_915026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915036 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 4]
def baseStart_915036 : Nat := 118140960795 + 915036 * 2 ^ 59
def prefixEnd_915036 : Nat := 4983230072969 + 3 ^ 40 * 915036 * 2
def baseEnd_915036 : Nat := 417647363704521912126073

theorem tailTrace_915036 : CollatzResearch.WordTrace tailWord_915036 prefixEnd_915036 417647363704521912126073 := by
  unfold tailWord_915036
  simp only [CollatzResearch.WordTrace]
  refine ⟨16687052356494161276082481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22249403141992215034776641 16687052356494161276082481)
  ·
    refine ⟨12515289267370620957061861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16687052356494161276082481 12515289267370620957061861)
    ·
      refine ⟨2346616737631991429449099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12515289267370620957061861 2346616737631991429449099)
      ·
        refine ⟨3519925106447987144173649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2346616737631991429449099 3519925106447987144173649)
        ·
          refine ⟨2639943829835990358130237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3519925106447987144173649 2639943829835990358130237)
          ·
            refine ⟨989978936188496384298839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2639943829835990358130237 989978936188496384298839)
            ·
              refine ⟨1484968404282744576448259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989978936188496384298839 1484968404282744576448259)
              ·
                refine ⟨2227452606424116864672389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484968404282744576448259 2227452606424116864672389)
                ·
                  refine ⟨417647363704521912126073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2227452606424116864672389 417647363704521912126073)
                  ·
                    rfl

theorem cell20_915036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_915036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915036 prefixEnd_915036 := by exact prefixLift 915036
  have htrace : WordTrace (prefixWord ++ tailWord_915036) baseStart_915036 baseEnd_915036 := by
    simpa [prefixWord, tailWord_915036, baseEnd_915036] using wordTrace_append hprefix tailTrace_915036
  have hstable : (prefixWord ++ tailWord_915036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915036).length < 2 ^ (prefixWord ++ tailWord_915036).sum := by decide
  have hdescent : baseEnd_915036 < baseStart_915036 := by decide
  rcases family_descends (prefixWord ++ tailWord_915036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915047 : List Nat := [1, 1, 5, 1, 1, 1, 3, 7]
def baseStart_915047 : Nat := 118140960795 + 915047 * 2 ^ 59
def prefixEnd_915047 : Nat := 4983230072969 + 3 ^ 40 * 915047 * 2
def baseEnd_915047 : Nat := 139217461468084920919787

theorem tailTrace_915047 : CollatzResearch.WordTrace tailWord_915047 prefixEnd_915047 139217461468084920919787 := by
  unfold tailWord_915047
  simp only [CollatzResearch.WordTrace]
  refine ⟨33374505915948471430815395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22249670610632314287210263 33374505915948471430815395)
  ·
    refine ⟨50061758873922707146223093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33374505915948471430815395 50061758873922707146223093)
    ·
      refine ⟨4693289894430253794958415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50061758873922707146223093 4693289894430253794958415)
      ·
        refine ⟨7039934841645380692437623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4693289894430253794958415 7039934841645380692437623)
        ·
          refine ⟨10559902262468071038656435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7039934841645380692437623 10559902262468071038656435)
          ·
            refine ⟨15839853393702106557984653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10559902262468071038656435 15839853393702106557984653)
            ·
              refine ⟨5939945022638289959244245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15839853393702106557984653 5939945022638289959244245)
              ·
                refine ⟨139217461468084920919787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5939945022638289959244245 139217461468084920919787)
                ·
                  rfl

theorem cell20_915047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 7].length) (baseStart_915047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915047 prefixEnd_915047 := by exact prefixLift 915047
  have htrace : WordTrace (prefixWord ++ tailWord_915047) baseStart_915047 baseEnd_915047 := by
    simpa [prefixWord, tailWord_915047, baseEnd_915047] using wordTrace_append hprefix tailTrace_915047
  have hstable : (prefixWord ++ tailWord_915047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915047).length < 2 ^ (prefixWord ++ tailWord_915047).sum := by decide
  have hdescent : baseEnd_915047 < baseStart_915047 := by decide
  rcases family_descends (prefixWord ++ tailWord_915047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915050 : List Nat := [3, 1, 3, 2, 1, 3, 1, 3, 3]
def baseStart_915050 : Nat := 118140960795 + 915050 * 2 ^ 59
def prefixEnd_915050 : Nat := 4983230072969 + 3 ^ 40 * 915050 * 2
def baseEnd_915050 : Nat := 417653753686000085659349

theorem tailTrace_915050 : CollatzResearch.WordTrace tailWord_915050 prefixEnd_915050 417653753686000085659349 := by
  unfold tailWord_915050
  simp only [CollatzResearch.WordTrace]
  refine ⟨8343653833734400735793651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22249743556625068628783069 8343653833734400735793651)
  ·
    refine ⟨12515480750601601103690477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8343653833734400735793651 12515480750601601103690477)
    ·
      refine ⟨4693305281475600413883929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12515480750601601103690477 4693305281475600413883929)
      ·
        refine ⟨3519978961106700310412947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4693305281475600413883929 3519978961106700310412947)
        ·
          refine ⟨5279968441660050465619421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519978961106700310412947 5279968441660050465619421)
          ·
            refine ⟨1979988165622518924607283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5279968441660050465619421 1979988165622518924607283)
            ·
              refine ⟨2969982248433778386910925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1979988165622518924607283 2969982248433778386910925)
              ·
                refine ⟨1113743343162666895091597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2969982248433778386910925 1113743343162666895091597)
                ·
                  refine ⟨417653753686000085659349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1113743343162666895091597 417653753686000085659349)
                  ·
                    rfl

theorem cell20_915050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_915050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915050 prefixEnd_915050 := by exact prefixLift 915050
  have htrace : WordTrace (prefixWord ++ tailWord_915050) baseStart_915050 baseEnd_915050 := by
    simpa [prefixWord, tailWord_915050, baseEnd_915050] using wordTrace_append hprefix tailTrace_915050
  have hstable : (prefixWord ++ tailWord_915050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915050).length < 2 ^ (prefixWord ++ tailWord_915050).sum := by decide
  have hdescent : baseEnd_915050 < baseStart_915050 := by decide
  rcases family_descends (prefixWord ++ tailWord_915050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915109 : List Nat := [1, 3, 1, 2, 1, 2, 4, 3, 3]
def baseStart_915109 : Nat := 118140960795 + 915109 * 2 ^ 59
def prefixEnd_915109 : Nat := 4983230072969 + 3 ^ 40 * 915109 * 2
def baseEnd_915109 : Nat := 417680682893658102692441

theorem tailTrace_915109 : CollatzResearch.WordTrace tailWord_915109 prefixEnd_915109 417680682893658102692441 := by
  unfold tailWord_915109
  simp only [CollatzResearch.WordTrace]
  refine ⟨33376767241723856019572381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22251178161149237346381587 33376767241723856019572381)
  ·
    refine ⟨12516287715646446007339643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33376767241723856019572381 12516287715646446007339643)
    ·
      refine ⟨18774431573469669011009465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12516287715646446007339643 18774431573469669011009465)
      ·
        refine ⟨14080823680102251758257099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18774431573469669011009465 14080823680102251758257099)
        ·
          refine ⟨21121235520153377637385649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14080823680102251758257099 21121235520153377637385649)
          ·
            refine ⟨15840926640115033228039237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21121235520153377637385649 15840926640115033228039237)
            ·
              refine ⟨2970173745021568730257357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15840926640115033228039237 2970173745021568730257357)
              ·
                refine ⟨1113815154383088273846509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2970173745021568730257357 1113815154383088273846509)
                ·
                  refine ⟨417680682893658102692441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1113815154383088273846509 417680682893658102692441)
                  ·
                    rfl

theorem cell20_915109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_915109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915109 prefixEnd_915109 := by exact prefixLift 915109
  have htrace : WordTrace (prefixWord ++ tailWord_915109) baseStart_915109 baseEnd_915109 := by
    simpa [prefixWord, tailWord_915109, baseEnd_915109] using wordTrace_append hprefix tailTrace_915109
  have hstable : (prefixWord ++ tailWord_915109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915109).length < 2 ^ (prefixWord ++ tailWord_915109).sum := by decide
  have hdescent : baseEnd_915109 < baseStart_915109 := by decide
  rcases family_descends (prefixWord ++ tailWord_915109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915178 : List Nat := [3, 1, 3, 1, 1, 1, 6, 4]
def baseStart_915178 : Nat := 118140960795 + 915178 * 2 ^ 59
def prefixEnd_915178 : Nat := 4983230072969 + 3 ^ 40 * 915178 * 2
def baseEnd_915178 : Nat := 139237392124600176464053

theorem tailTrace_915178 : CollatzResearch.WordTrace tailWord_915178 prefixEnd_915178 139237392124600176464053 := by
  unfold tailWord_915178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8344820969618470200958547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22252855918982587202556125 8344820969618470200958547)
  ·
    refine ⟨12517231454427705301437821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8344820969618470200958547 12517231454427705301437821)
    ·
      refine ⟨4693961795410389488039183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12517231454427705301437821 4693961795410389488039183)
      ·
        refine ⟨7040942693115584232058775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4693961795410389488039183 7040942693115584232058775)
        ·
          refine ⟨10561414039673376348088163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7040942693115584232058775 10561414039673376348088163)
          ·
            refine ⟨15842121059510064522132245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10561414039673376348088163 15842121059510064522132245)
            ·
              refine ⟨742599424664534274474949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15842121059510064522132245 742599424664534274474949)
              ·
                refine ⟨139237392124600176464053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 742599424664534274474949 139237392124600176464053)
                ·
                  rfl

theorem cell20_915178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_915178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915178 prefixEnd_915178 := by exact prefixLift 915178
  have htrace : WordTrace (prefixWord ++ tailWord_915178) baseStart_915178 baseEnd_915178 := by
    simpa [prefixWord, tailWord_915178, baseEnd_915178] using wordTrace_append hprefix tailTrace_915178
  have hstable : (prefixWord ++ tailWord_915178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915178).length < 2 ^ (prefixWord ++ tailWord_915178).sum := by decide
  have hdescent : baseEnd_915178 < baseStart_915178 := by decide
  rcases family_descends (prefixWord ++ tailWord_915178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915202 : List Nat := [3, 4, 1, 1, 1, 1, 2, 4, 3]
def baseStart_915202 : Nat := 118140960795 + 915202 * 2 ^ 59
def prefixEnd_915202 : Nat := 4983230072969 + 3 ^ 40 * 915202 * 2
def baseEnd_915202 : Nat := 417723130627763112592061

theorem tailTrace_915202 : CollatzResearch.WordTrace tailWord_915202 prefixEnd_915202 417723130627763112592061 := by
  unfold tailWord_915202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8345039807596733225676965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22253439486924621935138573 8345039807596733225676965)
  ·
    refine ⟨1564694963924387479814431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8345039807596733225676965 1564694963924387479814431)
    ·
      refine ⟨2347042445886581219721647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1564694963924387479814431 2347042445886581219721647)
      ·
        refine ⟨3520563668829871829582471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2347042445886581219721647 3520563668829871829582471)
        ·
          refine ⟨5280845503244807744373707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3520563668829871829582471 5280845503244807744373707)
          ·
            refine ⟨7921268254867211616560561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5280845503244807744373707 7921268254867211616560561)
            ·
              refine ⟨5940951191150408712420421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7921268254867211616560561 5940951191150408712420421)
              ·
                refine ⟨1113928348340701633578829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5940951191150408712420421 1113928348340701633578829)
                ·
                  refine ⟨417723130627763112592061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1113928348340701633578829 417723130627763112592061)
                  ·
                    rfl

theorem cell20_915202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_915202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915202 prefixEnd_915202 := by exact prefixLift 915202
  have htrace : WordTrace (prefixWord ++ tailWord_915202) baseStart_915202 baseEnd_915202 := by
    simpa [prefixWord, tailWord_915202, baseEnd_915202] using wordTrace_append hprefix tailTrace_915202
  have hstable : (prefixWord ++ tailWord_915202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915202).length < 2 ^ (prefixWord ++ tailWord_915202).sum := by decide
  have hdescent : baseEnd_915202 < baseStart_915202 := by decide
  rcases family_descends (prefixWord ++ tailWord_915202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915237 : List Nat := [1, 3, 1, 2, 3, 2, 2, 6]
def baseStart_915237 : Nat := 118140960795 + 915237 * 2 ^ 59
def prefixEnd_915237 : Nat := 4983230072969 + 3 ^ 40 * 915237 * 2
def baseEnd_915237 : Nat := 139246368527152848808417

theorem tailTrace_915237 : CollatzResearch.WordTrace tailWord_915237 prefixEnd_915237 139246368527152848808417 := by
  unfold tailWord_915237
  simp only [CollatzResearch.WordTrace]
  refine ⟨33381435785260133880231965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22254290523506755920154643 33381435785260133880231965)
  ·
    refine ⟨12518038419472550205086987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33381435785260133880231965 12518038419472550205086987)
    ·
      refine ⟨18777057629208825307630481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12518038419472550205086987 18777057629208825307630481)
      ·
        refine ⟨14082793221906618980722861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18777057629208825307630481 14082793221906618980722861)
        ·
          refine ⟨5281047458214982117771073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14082793221906618980722861 5281047458214982117771073)
          ·
            refine ⟨3960785593661236588328305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5281047458214982117771073 3960785593661236588328305)
            ·
              refine ⟨2970589195245927441246229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3960785593661236588328305 2970589195245927441246229)
              ·
                refine ⟨139246368527152848808417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2970589195245927441246229 139246368527152848808417)
                ·
                  rfl

theorem cell20_915237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 6].length) (baseStart_915237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915237 prefixEnd_915237 := by exact prefixLift 915237
  have htrace : WordTrace (prefixWord ++ tailWord_915237) baseStart_915237 baseEnd_915237 := by
    simpa [prefixWord, tailWord_915237, baseEnd_915237] using wordTrace_append hprefix tailTrace_915237
  have hstable : (prefixWord ++ tailWord_915237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915237).length < 2 ^ (prefixWord ++ tailWord_915237).sum := by decide
  have hdescent : baseEnd_915237 < baseStart_915237 := by decide
  rcases family_descends (prefixWord ++ tailWord_915237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915254 : List Nat := [5, 1, 2, 2, 1, 9]
def baseStart_915254 : Nat := 118140960795 + 915254 * 2 ^ 59
def prefixEnd_915254 : Nat := 4983230072969 + 3 ^ 40 * 915254 * 2
def baseEnd_915254 : Nat := 15472106105358594179945

theorem tailTrace_915254 : CollatzResearch.WordTrace tailWord_915254 prefixEnd_915254 15472106105358594179945 := by
  unfold tailWord_915254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2086378489137409111475051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22254703884132363855733877 2086378489137409111475051)
  ·
    refine ⟨3129567733706113667212577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2086378489137409111475051 3129567733706113667212577)
    ·
      refine ⟨2347175800279585250409433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3129567733706113667212577 2347175800279585250409433)
      ·
        refine ⟨1760381850209688937807075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2347175800279585250409433 1760381850209688937807075)
        ·
          refine ⟨2640572775314533406710613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1760381850209688937807075 2640572775314533406710613)
          ·
            refine ⟨15472106105358594179945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2640572775314533406710613 15472106105358594179945)
            ·
              rfl

theorem cell20_915254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 9].length) (baseStart_915254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915254 prefixEnd_915254 := by exact prefixLift 915254
  have htrace : WordTrace (prefixWord ++ tailWord_915254) baseStart_915254 baseEnd_915254 := by
    simpa [prefixWord, tailWord_915254, baseEnd_915254] using wordTrace_append hprefix tailTrace_915254
  have hstable : (prefixWord ++ tailWord_915254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915254).length < 2 ^ (prefixWord ++ tailWord_915254).sum := by decide
  have hdescent : baseEnd_915254 < baseStart_915254 := by decide
  rcases family_descends (prefixWord ++ tailWord_915254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915257 : List Nat := [1, 2, 1, 7, 1, 1, 2, 2, 3]
def baseStart_915257 : Nat := 118140960795 + 915257 * 2 ^ 59
def prefixEnd_915257 : Nat := 4983230072969 + 3 ^ 40 * 915257 * 2
def baseEnd_915257 : Nat := 417748234126427365758503

theorem tailTrace_915257 : CollatzResearch.WordTrace tailWord_915257 prefixEnd_915257 417748234126427365758503 := by
  unfold tailWord_915257
  simp only [CollatzResearch.WordTrace]
  refine ⟨33382165245187677295960025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22254776830125118197306683 33382165245187677295960025)
  ·
    refine ⟨25036623933890757971970019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33382165245187677295960025 25036623933890757971970019)
    ·
      refine ⟨37554935900836136957955029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25036623933890757971970019 37554935900836136957955029)
      ·
        refine ⟨880193810175846959952071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 37554935900836136957955029 880193810175846959952071)
        ·
          refine ⟨1320290715263770439928107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880193810175846959952071 1320290715263770439928107)
          ·
            refine ⟨1980436072895655659892161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320290715263770439928107 1980436072895655659892161)
            ·
              refine ⟨1485327054671741744919121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1980436072895655659892161 1485327054671741744919121)
              ·
                refine ⟨1113995291003806308689341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1485327054671741744919121 1113995291003806308689341)
                ·
                  refine ⟨417748234126427365758503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1113995291003806308689341 417748234126427365758503)
                  ·
                    rfl

theorem cell20_915257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_915257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915257 prefixEnd_915257 := by exact prefixLift 915257
  have htrace : WordTrace (prefixWord ++ tailWord_915257) baseStart_915257 baseEnd_915257 := by
    simpa [prefixWord, tailWord_915257, baseEnd_915257] using wordTrace_append hprefix tailTrace_915257
  have hstable : (prefixWord ++ tailWord_915257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915257).length < 2 ^ (prefixWord ++ tailWord_915257).sum := by decide
  have hdescent : baseEnd_915257 < baseStart_915257 := by decide
  rcases family_descends (prefixWord ++ tailWord_915257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915351 : List Nat := [1, 1, 3, 3, 1, 4, 1, 6]
def baseStart_915351 : Nat := 118140960795 + 915351 * 2 ^ 59
def prefixEnd_915351 : Nat := 4983230072969 + 3 ^ 40 * 915351 * 2
def baseEnd_915351 : Nat := 139263712762593605541595

theorem tailTrace_915351 : CollatzResearch.WordTrace tailWord_915351 prefixEnd_915351 139263712762593605541595 := by
  unfold tailWord_915351
  simp only [CollatzResearch.WordTrace]
  refine ⟨33385593706847131349881907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22257062471231420899921271 33385593706847131349881907)
  ·
    refine ⟨50078390560270697024822861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33385593706847131349881907 50078390560270697024822861)
    ·
      refine ⟨18779396460101511384308573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50078390560270697024822861 18779396460101511384308573)
      ·
        refine ⟨7042273672538066769115715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18779396460101511384308573 7042273672538066769115715)
        ·
          refine ⟨10563410508807100153673573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7042273672538066769115715 10563410508807100153673573)
          ·
            refine ⟨1980639470401331278813795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10563410508807100153673573 1980639470401331278813795)
            ·
              refine ⟨2970959205601996918220693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980639470401331278813795 2970959205601996918220693)
              ·
                refine ⟨139263712762593605541595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2970959205601996918220693 139263712762593605541595)
                ·
                  rfl

theorem cell20_915351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 6].length) (baseStart_915351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915351 prefixEnd_915351 := by exact prefixLift 915351
  have htrace : WordTrace (prefixWord ++ tailWord_915351) baseStart_915351 baseEnd_915351 := by
    simpa [prefixWord, tailWord_915351, baseEnd_915351] using wordTrace_append hprefix tailTrace_915351
  have hstable : (prefixWord ++ tailWord_915351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915351).length < 2 ^ (prefixWord ++ tailWord_915351).sum := by decide
  have hdescent : baseEnd_915351 < baseStart_915351 := by decide
  rcases family_descends (prefixWord ++ tailWord_915351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915365 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 6]
def baseStart_915365 : Nat := 118140960795 + 915365 * 2 ^ 59
def prefixEnd_915365 : Nat := 4983230072969 + 3 ^ 40 * 915365 * 2
def baseEnd_915365 : Nat := 417797528269258990158061

theorem tailTrace_915365 : CollatzResearch.WordTrace tailWord_915365 prefixEnd_915365 417797528269258990158061 := by
  unfold tailWord_915365
  simp only [CollatzResearch.WordTrace]
  refine ⟨33386104328796411740891549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22257402885864274493927699 33386104328796411740891549)
  ·
    refine ⟨12519789123298654402834331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33386104328796411740891549 12519789123298654402834331)
    ·
      refine ⟨18779683684947981604251497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12519789123298654402834331 18779683684947981604251497)
      ·
        refine ⟨14084762763710986203188623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18779683684947981604251497 14084762763710986203188623)
        ·
          refine ⟨21127144145566479304782935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14084762763710986203188623 21127144145566479304782935)
          ·
            refine ⟨31690716218349718957174403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21127144145566479304782935 31690716218349718957174403)
            ·
              refine ⟨47536074327524578435761605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31690716218349718957174403 47536074327524578435761605)
              ·
                refine ⟨8913013936410858456705301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47536074327524578435761605 8913013936410858456705301)
                ·
                  refine ⟨417797528269258990158061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8913013936410858456705301 417797528269258990158061)
                  ·
                    rfl

theorem cell20_915365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_915365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915365 prefixEnd_915365 := by exact prefixLift 915365
  have htrace : WordTrace (prefixWord ++ tailWord_915365) baseStart_915365 baseEnd_915365 := by
    simpa [prefixWord, tailWord_915365, baseEnd_915365] using wordTrace_append hprefix tailTrace_915365
  have hstable : (prefixWord ++ tailWord_915365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915365).length < 2 ^ (prefixWord ++ tailWord_915365).sum := by decide
  have hdescent : baseEnd_915365 < baseStart_915365 := by decide
  rcases family_descends (prefixWord ++ tailWord_915365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915374 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 4]
def baseStart_915374 : Nat := 118140960795 + 915374 * 2 ^ 59
def prefixEnd_915374 : Nat := 4983230072969 + 3 ^ 40 * 915374 * 2
def baseEnd_915374 : Nat := 417801636114494958858025

theorem tailTrace_915374 : CollatzResearch.WordTrace tailWord_915374 prefixEnd_915374 417801636114494958858025 := by
  unfold tailWord_915374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4173304073220475784746147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22257621723842537518646117 4173304073220475784746147)
  ·
    refine ⟨6259956109830713677119221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4173304073220475784746147 6259956109830713677119221)
    ·
      refine ⟨586870885296629407229927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6259956109830713677119221 586870885296629407229927)
      ·
        refine ⟨880306327944944110844891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586870885296629407229927 880306327944944110844891)
        ·
          refine ⟨1320459491917416166267337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880306327944944110844891 1320459491917416166267337)
          ·
            refine ⟨990344618938062124700503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1320459491917416166267337 990344618938062124700503)
            ·
              refine ⟨1485516928407093187050755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990344618938062124700503 1485516928407093187050755)
              ·
                refine ⟨2228275392610639780576133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485516928407093187050755 2228275392610639780576133)
                ·
                  refine ⟨417801636114494958858025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2228275392610639780576133 417801636114494958858025)
                  ·
                    rfl

theorem cell20_915374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_915374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915374 prefixEnd_915374 := by exact prefixLift 915374
  have htrace : WordTrace (prefixWord ++ tailWord_915374) baseStart_915374 baseEnd_915374 := by
    simpa [prefixWord, tailWord_915374, baseEnd_915374] using wordTrace_append hprefix tailTrace_915374
  have hstable : (prefixWord ++ tailWord_915374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915374).length < 2 ^ (prefixWord ++ tailWord_915374).sum := by decide
  have hdescent : baseEnd_915374 < baseStart_915374 := by decide
  rcases family_descends (prefixWord ++ tailWord_915374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915388 : List Nat := [2, 2, 2, 5, 1, 2, 2, 1, 3]
def baseStart_915388 : Nat := 118140960795 + 915388 * 2 ^ 59
def prefixEnd_915388 : Nat := 4983230072969 + 3 ^ 40 * 915388 * 2
def baseEnd_915388 : Nat := 417808026095973132391301

theorem tailTrace_915388 : CollatzResearch.WordTrace tailWord_915388 prefixEnd_915388 417808026095973132391301 := by
  unfold tailWord_915388
  simp only [CollatzResearch.WordTrace]
  refine ⟨16693471603856543334489409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22257962138475391112652545 16693471603856543334489409)
  ·
    refine ⟨12520103702892407500867057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16693471603856543334489409 12520103702892407500867057)
    ·
      refine ⟨9390077777169305625650293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12520103702892407500867057 9390077777169305625650293)
      ·
        refine ⟨880319791609622402404715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9390077777169305625650293 880319791609622402404715)
        ·
          refine ⟨1320479687414433603607073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880319791609622402404715 1320479687414433603607073)
          ·
            refine ⟨990359765560825202705305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1320479687414433603607073 990359765560825202705305)
            ·
              refine ⟨742769824170618902028979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 990359765560825202705305 742769824170618902028979)
              ·
                refine ⟨1114154736255928353043469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742769824170618902028979 1114154736255928353043469)
                ·
                  refine ⟨417808026095973132391301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114154736255928353043469 417808026095973132391301)
                  ·
                    rfl

theorem cell20_915388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_915388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915388 prefixEnd_915388 := by exact prefixLift 915388
  have htrace : WordTrace (prefixWord ++ tailWord_915388) baseStart_915388 baseEnd_915388 := by
    simpa [prefixWord, tailWord_915388, baseEnd_915388] using wordTrace_append hprefix tailTrace_915388
  have hstable : (prefixWord ++ tailWord_915388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915388).length < 2 ^ (prefixWord ++ tailWord_915388).sum := by decide
  have hdescent : baseEnd_915388 < baseStart_915388 := by decide
  rcases family_descends (prefixWord ++ tailWord_915388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915389 : List Nat := [1, 4, 1, 2, 3, 1, 1, 7]
def baseStart_915389 : Nat := 118140960795 + 915389 * 2 ^ 59
def prefixEnd_915389 : Nat := 4983230072969 + 3 ^ 40 * 915389 * 2
def baseEnd_915389 : Nat := 139269494174407191119321

theorem tailTrace_915389 : CollatzResearch.WordTrace tailWord_915389 prefixEnd_915389 139269494174407191119321 := by
  unfold tailWord_915389
  simp only [CollatzResearch.WordTrace]
  refine ⟨33386979680709463839765221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22257986453806309226510147 33386979680709463839765221)
  ·
    refine ⟨6260058690133024469955979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33386979680709463839765221 6260058690133024469955979)
    ·
      refine ⟨9390088035199536704933969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6260058690133024469955979 9390088035199536704933969)
      ·
        refine ⟨7042566026399652528700477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9390088035199536704933969 7042566026399652528700477)
        ·
          refine ⟨2640962259899869698262679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7042566026399652528700477 2640962259899869698262679)
          ·
            refine ⟨3961443389849804547394019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2640962259899869698262679 3961443389849804547394019)
            ·
              refine ⟨5942165084774706821091029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3961443389849804547394019 5942165084774706821091029)
              ·
                refine ⟨139269494174407191119321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5942165084774706821091029 139269494174407191119321)
                ·
                  rfl

theorem cell20_915389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 7].length) (baseStart_915389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915389 prefixEnd_915389 := by exact prefixLift 915389
  have htrace : WordTrace (prefixWord ++ tailWord_915389) baseStart_915389 baseEnd_915389 := by
    simpa [prefixWord, tailWord_915389, baseEnd_915389] using wordTrace_append hprefix tailTrace_915389
  have hstable : (prefixWord ++ tailWord_915389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915389).length < 2 ^ (prefixWord ++ tailWord_915389).sum := by decide
  have hdescent : baseEnd_915389 < baseStart_915389 := by decide
  rcases family_descends (prefixWord ++ tailWord_915389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915403 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 6]
def baseStart_915403 : Nat := 118140960795 + 915403 * 2 ^ 59
def prefixEnd_915403 : Nat := 4983230072969 + 3 ^ 40 * 915403 * 2
def baseEnd_915403 : Nat := 417814872504699746891239

theorem tailTrace_915403 : CollatzResearch.WordTrace tailWord_915403 prefixEnd_915403 417814872504699746891239 := by
  unfold tailWord_915403
  simp only [CollatzResearch.WordTrace]
  refine ⟨33387490302658744230774863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22258326868439162820516575 33387490302658744230774863)
  ·
    refine ⟨50081235453988116346162295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33387490302658744230774863 50081235453988116346162295)
    ·
      refine ⟨75121853180982174519243443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50081235453988116346162295 75121853180982174519243443)
      ·
        refine ⟨112682779771473261778865165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75121853180982174519243443 112682779771473261778865165)
        ·
          refine ⟨42256042414302473167074437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112682779771473261778865165 42256042414302473167074437)
          ·
            refine ⟨7923007952681713718826457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42256042414302473167074437 7923007952681713718826457)
            ·
              refine ⟨5942255964511285289119843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7923007952681713718826457 5942255964511285289119843)
              ·
                refine ⟨8913383946766927933679765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5942255964511285289119843 8913383946766927933679765)
                ·
                  refine ⟨417814872504699746891239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8913383946766927933679765 417814872504699746891239)
                  ·
                    rfl

theorem cell20_915403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_915403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915403 prefixEnd_915403 := by exact prefixLift 915403
  have htrace : WordTrace (prefixWord ++ tailWord_915403) baseStart_915403 baseEnd_915403 := by
    simpa [prefixWord, tailWord_915403, baseEnd_915403] using wordTrace_append hprefix tailTrace_915403
  have hstable : (prefixWord ++ tailWord_915403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915403).length < 2 ^ (prefixWord ++ tailWord_915403).sum := by decide
  have hdescent : baseEnd_915403 < baseStart_915403 := by decide
  rcases family_descends (prefixWord ++ tailWord_915403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915489 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 5]
def baseStart_915489 : Nat := 118140960795 + 915489 * 2 ^ 59
def prefixEnd_915489 : Nat := 4983230072969 + 3 ^ 40 * 915489 * 2
def baseEnd_915489 : Nat := 417854125248065670024221

theorem tailTrace_915489 : CollatzResearch.WordTrace tailWord_915489 prefixEnd_915489 417854125248065670024221 := by
  unfold tailWord_915489
  simp only [CollatzResearch.WordTrace]
  refine ⟨33390626980347180918405521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22260417986898120612270347 33390626980347180918405521)
  ·
    refine ⟨25042970235260385688804141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33390626980347180918405521 25042970235260385688804141)
    ·
      refine ⟨9391113838222644633301553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25042970235260385688804141 9391113838222644633301553)
      ·
        refine ⟨7043335378666983474976165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9391113838222644633301553 7043335378666983474976165)
        ·
          refine ⟨1320625383500059401558031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7043335378666983474976165 1320625383500059401558031)
          ·
            refine ⟨1980938075250089102337047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320625383500059401558031 1980938075250089102337047)
            ·
              refine ⟨2971407112875133653505571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980938075250089102337047 2971407112875133653505571)
              ·
                refine ⟨4457110669312700480258357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2971407112875133653505571 4457110669312700480258357)
                ·
                  refine ⟨417854125248065670024221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4457110669312700480258357 417854125248065670024221)
                  ·
                    rfl

theorem cell20_915489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_915489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915489 prefixEnd_915489 := by exact prefixLift 915489
  have htrace : WordTrace (prefixWord ++ tailWord_915489) baseStart_915489 baseEnd_915489 := by
    simpa [prefixWord, tailWord_915489, baseEnd_915489] using wordTrace_append hprefix tailTrace_915489
  have hstable : (prefixWord ++ tailWord_915489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915489).length < 2 ^ (prefixWord ++ tailWord_915489).sum := by decide
  have hdescent : baseEnd_915489 < baseStart_915489 := by decide
  rcases family_descends (prefixWord ++ tailWord_915489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915506 : List Nat := [3, 2, 1, 1, 2, 4, 3, 1, 3]
def baseStart_915506 : Nat := 118140960795 + 915506 * 2 ^ 59
def prefixEnd_915506 : Nat := 4983230072969 + 3 ^ 40 * 915506 * 2
def baseEnd_915506 : Nat := 417861884511289166457485

theorem tailTrace_915506 : CollatzResearch.WordTrace tailWord_915506 prefixEnd_915506 417861884511289166457485 := by
  unfold tailWord_915506
  simp only [CollatzResearch.WordTrace]
  refine ⟨8347811755321398205443593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22260831347523728547849581 8347811755321398205443593)
  ·
    refine ⟨6260858816491048654082695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8347811755321398205443593 6260858816491048654082695)
    ·
      refine ⟨9391288224736572981124043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6260858816491048654082695 9391288224736572981124043)
      ·
        refine ⟨14086932337104859471686065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9391288224736572981124043 14086932337104859471686065)
        ·
          refine ⟨10565199252828644603764549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14086932337104859471686065 10565199252828644603764549)
          ·
            refine ⟨1980974859905370863205853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10565199252828644603764549 1980974859905370863205853)
            ·
              refine ⟨742865572464514073702195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1980974859905370863205853 742865572464514073702195)
              ·
                refine ⟨1114298358696771110553293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742865572464514073702195 1114298358696771110553293)
                ·
                  refine ⟨417861884511289166457485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114298358696771110553293 417861884511289166457485)
                  ·
                    rfl

theorem cell20_915506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_915506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915506 prefixEnd_915506 := by exact prefixLift 915506
  have htrace : WordTrace (prefixWord ++ tailWord_915506) baseStart_915506 baseEnd_915506 := by
    simpa [prefixWord, tailWord_915506, baseEnd_915506] using wordTrace_append hprefix tailTrace_915506
  have hstable : (prefixWord ++ tailWord_915506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915506).length < 2 ^ (prefixWord ++ tailWord_915506).sum := by decide
  have hdescent : baseEnd_915506 < baseStart_915506 := by decide
  rcases family_descends (prefixWord ++ tailWord_915506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915520 : List Nat := [2, 1, 1, 2, 2, 6, 2, 4]
def baseStart_915520 : Nat := 118140960795 + 915520 * 2 ^ 59
def prefixEnd_915520 : Nat := 4983230072969 + 3 ^ 40 * 915520 * 2
def baseEnd_915520 : Nat := 139289424830922446663587

theorem tailTrace_915520 : CollatzResearch.WordTrace tailWord_915520 prefixEnd_915520 139289424830922446663587 := by
  unfold tailWord_915520
  simp only [CollatzResearch.WordTrace]
  refine ⟨16695878821617436606392007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22261171762156582141856009 16695878821617436606392007)
  ·
    refine ⟨25043818232426154909588011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16695878821617436606392007 25043818232426154909588011)
    ·
      refine ⟨37565727348639232364382017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25043818232426154909588011 37565727348639232364382017)
      ·
        refine ⟨28174295511479424273286513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37565727348639232364382017 28174295511479424273286513)
        ·
          refine ⟨21130721633609568204964885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28174295511479424273286513 21130721633609568204964885)
          ·
            refine ⟨990502576575448509607729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21130721633609568204964885 990502576575448509607729)
            ·
              refine ⟨742876932431586382205797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 990502576575448509607729 742876932431586382205797)
              ·
                refine ⟨139289424830922446663587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 742876932431586382205797 139289424830922446663587)
                ·
                  rfl

theorem cell20_915520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_915520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915520 prefixEnd_915520 := by exact prefixLift 915520
  have htrace : WordTrace (prefixWord ++ tailWord_915520) baseStart_915520 baseEnd_915520 := by
    simpa [prefixWord, tailWord_915520, baseEnd_915520] using wordTrace_append hprefix tailTrace_915520
  have hstable : (prefixWord ++ tailWord_915520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915520).length < 2 ^ (prefixWord ++ tailWord_915520).sum := by decide
  have hdescent : baseEnd_915520 < baseStart_915520 := by decide
  rcases family_descends (prefixWord ++ tailWord_915520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915541 : List Nat := [1, 3, 2, 2, 1, 5, 6]
def baseStart_915541 : Nat := 118140960795 + 915541 * 2 ^ 59
def prefixEnd_915541 : Nat := 4983230072969 + 3 ^ 40 * 915541 * 2
def baseEnd_915541 : Nat := 46430873273887177810075

theorem tailTrace_915541 : CollatzResearch.WordTrace tailWord_915541 prefixEnd_915541 46430873273887177810075 := by
  unfold tailWord_915541
  simp only [CollatzResearch.WordTrace]
  refine ⟨33392523576158793799298477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22261682384105862532865651 33392523576158793799298477)
  ·
    refine ⟨12522196341059547674736929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33392523576158793799298477 12522196341059547674736929)
    ·
      refine ⟨9391647255794660756052697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12522196341059547674736929 9391647255794660756052697)
      ·
        refine ⟨7043735441845995567039523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9391647255794660756052697 7043735441845995567039523)
        ·
          refine ⟨10565603162768993350559285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7043735441845995567039523 10565603162768993350559285)
          ·
            refine ⟨990525296509593126614933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10565603162768993350559285 990525296509593126614933)
            ·
              refine ⟨46430873273887177810075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 990525296509593126614933 46430873273887177810075)
              ·
                rfl

theorem cell20_915541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 6].length) (baseStart_915541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915541 prefixEnd_915541 := by exact prefixLift 915541
  have htrace : WordTrace (prefixWord ++ tailWord_915541) baseStart_915541 baseEnd_915541 := by
    simpa [prefixWord, tailWord_915541, baseEnd_915541] using wordTrace_append hprefix tailTrace_915541
  have hstable : (prefixWord ++ tailWord_915541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915541).length < 2 ^ (prefixWord ++ tailWord_915541).sum := by decide
  have hdescent : baseEnd_915541 < baseStart_915541 := by decide
  rcases family_descends (prefixWord ++ tailWord_915541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915565 : List Nat := [1, 5, 1, 1, 2, 1, 3, 3, 3]
def baseStart_915565 : Nat := 118140960795 + 915565 * 2 ^ 59
def prefixEnd_915565 : Nat := 4983230072969 + 3 ^ 40 * 915565 * 2
def baseEnd_915565 : Nat := 417888813718947183490577

theorem tailTrace_915565 : CollatzResearch.WordTrace tailWord_915565 prefixEnd_915565 417888813718947183490577 := by
  unfold tailWord_915565
  simp only [CollatzResearch.WordTrace]
  refine ⟨33393398928071845898172149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22262265952047897265448099 33393398928071845898172149)
  ·
    refine ⟨3130631149506735552953639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33393398928071845898172149 3130631149506735552953639)
    ·
      refine ⟨4695946724260103329430459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3130631149506735552953639 4695946724260103329430459)
      ·
        refine ⟨7043920086390154994145689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4695946724260103329430459 7043920086390154994145689)
        ·
          refine ⟨5282940064792616245609267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7043920086390154994145689 5282940064792616245609267)
          ·
            refine ⟨7924410097188924368413901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5282940064792616245609267 7924410097188924368413901)
            ·
              refine ⟨2971653786445846638155213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7924410097188924368413901 2971653786445846638155213)
              ·
                refine ⟨1114370169917192489308205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2971653786445846638155213 1114370169917192489308205)
                ·
                  refine ⟨417888813718947183490577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114370169917192489308205 417888813718947183490577)
                  ·
                    rfl

theorem cell20_915565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_915565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915565 prefixEnd_915565 := by exact prefixLift 915565
  have htrace : WordTrace (prefixWord ++ tailWord_915565) baseStart_915565 baseEnd_915565 := by
    simpa [prefixWord, tailWord_915565, baseEnd_915565] using wordTrace_append hprefix tailTrace_915565
  have hstable : (prefixWord ++ tailWord_915565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915565).length < 2 ^ (prefixWord ++ tailWord_915565).sum := by decide
  have hdescent : baseEnd_915565 < baseStart_915565 := by decide
  rcases family_descends (prefixWord ++ tailWord_915565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915617 : List Nat := [1, 2, 3, 3, 1, 2, 3, 5]
def baseStart_915617 : Nat := 118140960795 + 915617 * 2 ^ 59
def prefixEnd_915617 : Nat := 4983230072969 + 3 ^ 40 * 915617 * 2
def baseEnd_915617 : Nat := 139304182645288704585677

theorem tailTrace_915617 : CollatzResearch.WordTrace tailWord_915617 prefixEnd_915617 139304182645288704585677 := by
  unfold tailWord_915617
  simp only [CollatzResearch.WordTrace]
  refine ⟨33395295523883458779065105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22263530349255639186043403 33395295523883458779065105)
  ·
    refine ⟨25046471642912594084298829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33395295523883458779065105 25046471642912594084298829)
    ·
      refine ⟨9392426866092222781612061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25046471642912594084298829 9392426866092222781612061)
      ·
        refine ⟨3522160074784583543104523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9392426866092222781612061 3522160074784583543104523)
        ·
          refine ⟨5283240112176875314656785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3522160074784583543104523 5283240112176875314656785)
          ·
            refine ⟨3962430084132656485992589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5283240112176875314656785 3962430084132656485992589)
            ·
              refine ⟨1485911281549746182247221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3962430084132656485992589 1485911281549746182247221)
              ·
                refine ⟨139304182645288704585677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1485911281549746182247221 139304182645288704585677)
                ·
                  rfl

theorem cell20_915617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 5].length) (baseStart_915617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915617 prefixEnd_915617 := by exact prefixLift 915617
  have htrace : WordTrace (prefixWord ++ tailWord_915617) baseStart_915617 baseEnd_915617 := by
    simpa [prefixWord, tailWord_915617, baseEnd_915617] using wordTrace_append hprefix tailTrace_915617
  have hstable : (prefixWord ++ tailWord_915617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915617).length < 2 ^ (prefixWord ++ tailWord_915617).sum := by decide
  have hdescent : baseEnd_915617 < baseStart_915617 := by decide
  rcases family_descends (prefixWord ++ tailWord_915617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915630 : List Nat := [4, 1, 4, 2, 1, 1, 3, 4]
def baseStart_915630 : Nat := 118140960795 + 915630 * 2 ^ 59
def prefixEnd_915630 : Nat := 4983230072969 + 3 ^ 40 * 915630 * 2
def baseEnd_915630 : Nat := 139306160496698615441215

theorem tailTrace_915630 : CollatzResearch.WordTrace tailWord_915630 prefixEnd_915630 139306160496698615441215 := by
  unfold tailWord_915630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4174471209104545249911043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22263846448557574666192229 4174471209104545249911043)
  ·
    refine ⟨6261706813656817874866565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4174471209104545249911043 6261706813656817874866565)
    ·
      refine ⟨1174070027560653351537481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6261706813656817874866565 1174070027560653351537481)
      ·
        refine ⟨880552520670490013653111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1174070027560653351537481 880552520670490013653111)
        ·
          refine ⟨1320828781005735020479667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880552520670490013653111 1320828781005735020479667)
          ·
            refine ⟨1981243171508602530719501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320828781005735020479667 1981243171508602530719501)
            ·
              refine ⟨742966189315725949019813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1981243171508602530719501 742966189315725949019813)
              ·
                refine ⟨139306160496698615441215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 742966189315725949019813 139306160496698615441215)
                ·
                  rfl

theorem cell20_915630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_915630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915630 prefixEnd_915630 := by exact prefixLift 915630
  have htrace : WordTrace (prefixWord ++ tailWord_915630) baseStart_915630 baseEnd_915630 := by
    simpa [prefixWord, tailWord_915630, baseEnd_915630] using wordTrace_append hprefix tailTrace_915630
  have hstable : (prefixWord ++ tailWord_915630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915630).length < 2 ^ (prefixWord ++ tailWord_915630).sum := by decide
  have hdescent : baseEnd_915630 < baseStart_915630 := by decide
  rcases family_descends (prefixWord ++ tailWord_915630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915644 : List Nat := [2, 2, 2, 3, 3, 1, 2, 3, 2]
def baseStart_915644 : Nat := 118140960795 + 915644 * 2 ^ 59
def prefixEnd_915644 : Nat := 4983230072969 + 3 ^ 40 * 915644 * 2
def baseEnd_915644 : Nat := 417924871471574019856921

theorem tailTrace_915644 : CollatzResearch.WordTrace tailWord_915644 prefixEnd_915644 417924871471574019856921 := by
  unfold tailWord_915644
  simp only [CollatzResearch.WordTrace]
  refine ⟨16698140147392821195148993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22264186863190428260198657 16698140147392821195148993)
  ·
    refine ⟨12523605110544615896361745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16698140147392821195148993 12523605110544615896361745)
    ·
      refine ⟨9392703832908461922271309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12523605110544615896361745 9392703832908461922271309)
      ·
        refine ⟨3522263937340673220851741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9392703832908461922271309 3522263937340673220851741)
        ·
          refine ⟨1320848976502752457819403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3522263937340673220851741 1320848976502752457819403)
          ·
            refine ⟨1981273464754128686729105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320848976502752457819403 1981273464754128686729105)
            ·
              refine ⟨1485955098565596515046829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1981273464754128686729105 1485955098565596515046829)
              ·
                refine ⟨557233161962098693142561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1485955098565596515046829 557233161962098693142561)
                ·
                  refine ⟨417924871471574019856921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557233161962098693142561 417924871471574019856921)
                  ·
                    rfl

theorem cell20_915644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_915644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915644 prefixEnd_915644 := by exact prefixLift 915644
  have htrace : WordTrace (prefixWord ++ tailWord_915644) baseStart_915644 baseEnd_915644 := by
    simpa [prefixWord, tailWord_915644, baseEnd_915644] using wordTrace_append hprefix tailTrace_915644
  have hstable : (prefixWord ++ tailWord_915644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915644).length < 2 ^ (prefixWord ++ tailWord_915644).sum := by decide
  have hdescent : baseEnd_915644 < baseStart_915644 := by decide
  rcases family_descends (prefixWord ++ tailWord_915644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915720 : List Nat := [2, 1, 3, 2, 3, 2, 3, 2, 2]
def baseStart_915720 : Nat := 118140960795 + 915720 * 2 ^ 59
def prefixEnd_915720 : Nat := 4983230072969 + 3 ^ 40 * 915720 * 2
def baseEnd_915720 : Nat := 417959559942455533323277

theorem tailTrace_915720 : CollatzResearch.WordTrace tailWord_915720 prefixEnd_915720 417959559942455533323277 := by
  unfold tailWord_915720
  simp only [CollatzResearch.WordTrace]
  refine ⟨16699526121255153685032307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22266034828340204913376409 16699526121255153685032307)
  ·
    refine ⟨25049289181882730527548461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16699526121255153685032307 25049289181882730527548461)
    ·
      refine ⟨9393483443206023947830673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25049289181882730527548461 9393483443206023947830673)
      ·
        refine ⟨7045112582404517960873005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9393483443206023947830673 7045112582404517960873005)
        ·
          refine ⟨2641917218401694235327377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7045112582404517960873005 2641917218401694235327377)
          ·
            refine ⟨1981437913801270676495533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2641917218401694235327377 1981437913801270676495533)
            ·
              refine ⟨743039217675476503685825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1981437913801270676495533 743039217675476503685825)
              ·
                refine ⟨557279413256607377764369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 743039217675476503685825 557279413256607377764369)
                ·
                  refine ⟨417959559942455533323277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557279413256607377764369 417959559942455533323277)
                  ·
                    rfl

theorem cell20_915720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 2].length) (baseStart_915720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915720 prefixEnd_915720 := by exact prefixLift 915720
  have htrace : WordTrace (prefixWord ++ tailWord_915720) baseStart_915720 baseEnd_915720 := by
    simpa [prefixWord, tailWord_915720, baseEnd_915720] using wordTrace_append hprefix tailTrace_915720
  have hstable : (prefixWord ++ tailWord_915720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915720).length < 2 ^ (prefixWord ++ tailWord_915720).sum := by decide
  have hdescent : baseEnd_915720 < baseStart_915720 := by decide
  rcases family_descends (prefixWord ++ tailWord_915720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915745 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 4]
def baseStart_915745 : Nat := 118140960795 + 915745 * 2 ^ 59
def prefixEnd_915745 : Nat := 4983230072969 + 3 ^ 40 * 915745 * 2
def baseEnd_915745 : Nat := 417970970623666557489841

theorem tailTrace_915745 : CollatzResearch.WordTrace tailWord_915745 prefixEnd_915745 417970970623666557489841 := by
  unfold tailWord_915745
  simp only [CollatzResearch.WordTrace]
  refine ⟨33399964067419736639724689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22266642711613157759816459 33399964067419736639724689)
  ·
    refine ⟨25049973050564802479793517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33399964067419736639724689 25049973050564802479793517)
    ·
      refine ⟨9393739893961800929922569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25049973050564802479793517 9393739893961800929922569)
      ·
        refine ⟨7045304920471350697441927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9393739893961800929922569 7045304920471350697441927)
        ·
          refine ⟨10567957380707026046162891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7045304920471350697441927 10567957380707026046162891)
          ·
            refine ⟨15851936071060539069244337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10567957380707026046162891 15851936071060539069244337)
            ·
              refine ⟨11888952053295404301933253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15851936071060539069244337 11888952053295404301933253)
              ·
                refine ⟨2229178509992888306612485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11888952053295404301933253 2229178509992888306612485)
                ·
                  refine ⟨417970970623666557489841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2229178509992888306612485 417970970623666557489841)
                  ·
                    rfl

theorem cell20_915745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_915745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915745 prefixEnd_915745 := by exact prefixLift 915745
  have htrace : WordTrace (prefixWord ++ tailWord_915745) baseStart_915745 baseEnd_915745 := by
    simpa [prefixWord, tailWord_915745, baseEnd_915745] using wordTrace_append hprefix tailTrace_915745
  have hstable : (prefixWord ++ tailWord_915745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915745).length < 2 ^ (prefixWord ++ tailWord_915745).sum := by decide
  have hdescent : baseEnd_915745 < baseStart_915745 := by decide
  rcases family_descends (prefixWord ++ tailWord_915745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915759 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 7]
def baseStart_915759 : Nat := 118140960795 + 915759 * 2 ^ 59
def prefixEnd_915759 : Nat := 4983230072969 + 3 ^ 40 * 915759 * 2
def baseEnd_915759 : Nat := 417977360605144731023117

theorem tailTrace_915759 : CollatzResearch.WordTrace tailWord_915759 prefixEnd_915759 417977360605144731023117 := by
  unfold tailWord_915759
  simp only [CollatzResearch.WordTrace]
  refine ⟨33400474689369017030734331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22266983126246011353822887 33400474689369017030734331)
  ·
    refine ⟨50100712034053525546101497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33400474689369017030734331 50100712034053525546101497)
    ·
      refine ⟨37575534025540144159576123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50100712034053525546101497 37575534025540144159576123)
      ·
        refine ⟨56363301038310216239364185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37575534025540144159576123 56363301038310216239364185)
        ·
          refine ⟨42272475778732662179523139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56363301038310216239364185 42272475778732662179523139)
          ·
            refine ⟨63408713668098993269284709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42272475778732662179523139 63408713668098993269284709)
            ·
              refine ⟨11889133812768561237990883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63408713668098993269284709 11889133812768561237990883)
              ·
                refine ⟨17833700719152841856986325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11889133812768561237990883 17833700719152841856986325)
                ·
                  refine ⟨417977360605144731023117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17833700719152841856986325 417977360605144731023117)
                  ·
                    rfl

theorem cell20_915759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_915759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915759 prefixEnd_915759 := by exact prefixLift 915759
  have htrace : WordTrace (prefixWord ++ tailWord_915759) baseStart_915759 baseEnd_915759 := by
    simpa [prefixWord, tailWord_915759, baseEnd_915759] using wordTrace_append hprefix tailTrace_915759
  have hstable : (prefixWord ++ tailWord_915759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915759).length < 2 ^ (prefixWord ++ tailWord_915759).sum := by decide
  have hdescent : baseEnd_915759 < baseStart_915759 := by decide
  rcases family_descends (prefixWord ++ tailWord_915759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915779 : List Nat := [1, 1, 1, 3, 1, 3, 6, 2, 2]
def baseStart_915779 : Nat := 118140960795 + 915779 * 2 ^ 59
def prefixEnd_915779 : Nat := 4983230072969 + 3 ^ 40 * 915779 * 2
def baseEnd_915779 : Nat := 417986489150113550356369

theorem tailTrace_915779 : CollatzResearch.WordTrace tailWord_915779 prefixEnd_915779 417986489150113550356369 := by
  unfold tailWord_915779
  simp only [CollatzResearch.WordTrace]
  refine ⟨33401204149296560446462391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22267469432864373630974927 33401204149296560446462391)
  ·
    refine ⟨50101806223944840669693587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33401204149296560446462391 50101806223944840669693587)
    ·
      refine ⟨75152709335917261004540381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50101806223944840669693587 75152709335917261004540381)
      ·
        refine ⟨28182266000968972876702643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75152709335917261004540381 28182266000968972876702643)
        ·
          refine ⟨42273399001453459315053965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28182266000968972876702643 42273399001453459315053965)
          ·
            refine ⟨15852524625545047243145237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42273399001453459315053965 15852524625545047243145237)
            ·
              refine ⟨743087091822424089522433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15852524625545047243145237 743087091822424089522433)
              ·
                refine ⟨557315318866818067141825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 743087091822424089522433 557315318866818067141825)
                ·
                  refine ⟨417986489150113550356369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557315318866818067141825 417986489150113550356369)
                  ·
                    rfl

theorem cell20_915779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 2].length) (baseStart_915779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915779 prefixEnd_915779 := by exact prefixLift 915779
  have htrace : WordTrace (prefixWord ++ tailWord_915779) baseStart_915779 baseEnd_915779 := by
    simpa [prefixWord, tailWord_915779, baseEnd_915779] using wordTrace_append hprefix tailTrace_915779
  have hstable : (prefixWord ++ tailWord_915779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915779).length < 2 ^ (prefixWord ++ tailWord_915779).sum := by decide
  have hdescent : baseEnd_915779 < baseStart_915779 := by decide
  rcases family_descends (prefixWord ++ tailWord_915779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915783 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 4]
def baseStart_915783 : Nat := 118140960795 + 915783 * 2 ^ 59
def prefixEnd_915783 : Nat := 4983230072969 + 3 ^ 40 * 915783 * 2
def baseEnd_915783 : Nat := 417988314859107314223019

theorem tailTrace_915783 : CollatzResearch.WordTrace tailWord_915783 prefixEnd_915783 417988314859107314223019 := by
  unfold tailWord_915783
  simp only [CollatzResearch.WordTrace]
  refine ⟨33401350041282069129608003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22267566694188046086405335 33401350041282069129608003)
  ·
    refine ⟨50102025061923103694412005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33401350041282069129608003 50102025061923103694412005)
    ·
      refine ⟨9394129699110581942702251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50102025061923103694412005 9394129699110581942702251)
      ·
        refine ⟨14091194548665872914053377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9394129699110581942702251 14091194548665872914053377)
        ·
          refine ⟨10568395911499404685540033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14091194548665872914053377 10568395911499404685540033)
          ·
            refine ⟨7926296933624553514155025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10568395911499404685540033 7926296933624553514155025)
            ·
              refine ⟨5944722700218415135616269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7926296933624553514155025 5944722700218415135616269)
              ·
                refine ⟨2229271012581905675856101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5944722700218415135616269 2229271012581905675856101)
                ·
                  refine ⟨417988314859107314223019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2229271012581905675856101 417988314859107314223019)
                  ·
                    rfl

theorem cell20_915783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_915783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915783 prefixEnd_915783 := by exact prefixLift 915783
  have htrace : WordTrace (prefixWord ++ tailWord_915783) baseStart_915783 baseEnd_915783 := by
    simpa [prefixWord, tailWord_915783, baseEnd_915783] using wordTrace_append hprefix tailTrace_915783
  have hstable : (prefixWord ++ tailWord_915783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915783).length < 2 ^ (prefixWord ++ tailWord_915783).sum := by decide
  have hdescent : baseEnd_915783 < baseStart_915783 := by decide
  rcases family_descends (prefixWord ++ tailWord_915783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915790 : List Nat := [4, 1, 1, 1, 1, 1, 2, 9]
def baseStart_915790 : Nat := 118140960795 + 915790 * 2 ^ 59
def prefixEnd_915790 : Nat := 4983230072969 + 3 ^ 40 * 915790 * 2
def baseEnd_915790 : Nat := 139330503283282133663219

theorem tailTrace_915790 : CollatzResearch.WordTrace tailWord_915790 prefixEnd_915790 139330503283282133663219 := by
  unfold tailWord_915790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4175200669032088665639103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22267736901504472883408549 4175200669032088665639103)
  ·
    refine ⟨6262801003548132998458655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4175200669032088665639103 6262801003548132998458655)
    ·
      refine ⟨9394201505322199497687983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6262801003548132998458655 9394201505322199497687983)
      ·
        refine ⟨14091302257983299246531975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9394201505322199497687983 14091302257983299246531975)
        ·
          refine ⟨21136953386974948869797963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14091302257983299246531975 21136953386974948869797963)
          ·
            refine ⟨31705430080462423304696945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21136953386974948869797963 31705430080462423304696945)
            ·
              refine ⟨23779072560346817478522709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31705430080462423304696945 23779072560346817478522709)
              ·
                refine ⟨139330503283282133663219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23779072560346817478522709 139330503283282133663219)
                ·
                  rfl

theorem cell20_915790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_915790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915790 prefixEnd_915790 := by exact prefixLift 915790
  have htrace : WordTrace (prefixWord ++ tailWord_915790) baseStart_915790 baseEnd_915790 := by
    simpa [prefixWord, tailWord_915790, baseEnd_915790] using wordTrace_append hprefix tailTrace_915790
  have hstable : (prefixWord ++ tailWord_915790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915790).length < 2 ^ (prefixWord ++ tailWord_915790).sum := by decide
  have hdescent : baseEnd_915790 < baseStart_915790 := by decide
  rcases family_descends (prefixWord ++ tailWord_915790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915821 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 6]
def baseStart_915821 : Nat := 118140960795 + 915821 * 2 ^ 59
def prefixEnd_915821 : Nat := 4983230072969 + 3 ^ 40 * 915821 * 2
def baseEnd_915821 : Nat := 418005659094548070956197

theorem tailTrace_915821 : CollatzResearch.WordTrace tailWord_915821 prefixEnd_915821 418005659094548070956197 := by
  unfold tailWord_915821
  simp only [CollatzResearch.WordTrace]
  refine ⟨33402736015144401619491317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22268490676762934412994211 33402736015144401619491317)
  ·
    refine ⟨3131506501419787651827311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33402736015144401619491317 3131506501419787651827311)
    ·
      refine ⟨4697259752129681477740967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3131506501419787651827311 4697259752129681477740967)
      ·
        refine ⟨7045889628194522216611451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4697259752129681477740967 7045889628194522216611451)
        ·
          refine ⟨10568834442291783324917177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7045889628194522216611451 10568834442291783324917177)
          ·
            refine ⟨7926625831718837493687883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10568834442291783324917177 7926625831718837493687883)
            ·
              refine ⟨11889938747578256240531825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7926625831718837493687883 11889938747578256240531825)
              ·
                refine ⟨8917454060683692180398869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11889938747578256240531825 8917454060683692180398869)
                ·
                  refine ⟨418005659094548070956197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8917454060683692180398869 418005659094548070956197)
                  ·
                    rfl

theorem cell20_915821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_915821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915821 prefixEnd_915821 := by exact prefixLift 915821
  have htrace : WordTrace (prefixWord ++ tailWord_915821) baseStart_915821 baseEnd_915821 := by
    simpa [prefixWord, tailWord_915821, baseEnd_915821] using wordTrace_append hprefix tailTrace_915821
  have hstable : (prefixWord ++ tailWord_915821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915821).length < 2 ^ (prefixWord ++ tailWord_915821).sum := by decide
  have hdescent : baseEnd_915821 < baseStart_915821 := by decide
  rcases family_descends (prefixWord ++ tailWord_915821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915890 : List Nat := [3, 2, 1, 1, 1, 1, 4, 4, 3]
def baseStart_915890 : Nat := 118140960795 + 915890 * 2 ^ 59
def prefixEnd_915890 : Nat := 4983230072969 + 3 ^ 40 * 915890 * 2
def baseEnd_915890 : Nat := 418037152574690497655915

theorem tailTrace_915890 : CollatzResearch.WordTrace tailWord_915890 prefixEnd_915890 418037152574690497655915 := by
  unfold tailWord_915890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8351313162973606600938281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22270168434596284269168749 8351313162973606600938281)
  ·
    refine ⟨6263484872230204950703711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8351313162973606600938281 6263484872230204950703711)
    ·
      refine ⟨9395227308345307426055567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6263484872230204950703711 9395227308345307426055567)
      ·
        refine ⟨14092840962517961139083351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9395227308345307426055567 14092840962517961139083351)
        ·
          refine ⟨21139261443776941708625027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14092840962517961139083351 21139261443776941708625027)
          ·
            refine ⟨31708892165665412562937541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21139261443776941708625027 31708892165665412562937541)
            ·
              refine ⟨5945417281062264855550789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31708892165665412562937541 5945417281062264855550789)
              ·
                refine ⟨1114765740199174660415773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5945417281062264855550789 1114765740199174660415773)
                ·
                  refine ⟨418037152574690497655915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114765740199174660415773 418037152574690497655915)
                  ·
                    rfl

theorem cell20_915890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_915890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915890 prefixEnd_915890 := by exact prefixLift 915890
  have htrace : WordTrace (prefixWord ++ tailWord_915890) baseStart_915890 baseEnd_915890 := by
    simpa [prefixWord, tailWord_915890, baseEnd_915890] using wordTrace_append hprefix tailTrace_915890
  have hstable : (prefixWord ++ tailWord_915890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915890).length < 2 ^ (prefixWord ++ tailWord_915890).sum := by decide
  have hdescent : baseEnd_915890 < baseStart_915890 := by decide
  rcases family_descends (prefixWord ++ tailWord_915890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915893 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 4]
def baseStart_915893 : Nat := 118140960795 + 915893 * 2 ^ 59
def prefixEnd_915893 : Nat := 4983230072969 + 3 ^ 40 * 915893 * 2
def baseEnd_915893 : Nat := 418038521856435820555903

theorem tailTrace_915893 : CollatzResearch.WordTrace tailWord_915893 prefixEnd_915893 418038521856435820555903 := by
  unfold tailWord_915893
  simp only [CollatzResearch.WordTrace]
  refine ⟨33405362070883557916112333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22270241380589038610741555 33405362070883557916112333)
  ·
    refine ⟨12527010776581334218542125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33405362070883557916112333 12527010776581334218542125)
    ·
      refine ⟨4697629041218000331953297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12527010776581334218542125 4697629041218000331953297)
      ·
        refine ⟨3523221780913500248964973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4697629041218000331953297 3523221780913500248964973)
        ·
          refine ⟨1321208167842562593361865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3523221780913500248964973 1321208167842562593361865)
          ·
            refine ⟨990906125881921945021399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1321208167842562593361865 990906125881921945021399)
            ·
              refine ⟨1486359188822882917532099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990906125881921945021399 1486359188822882917532099)
              ·
                refine ⟨2229538783234324376298149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1486359188822882917532099 2229538783234324376298149)
                ·
                  refine ⟨418038521856435820555903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2229538783234324376298149 418038521856435820555903)
                  ·
                    rfl

theorem cell20_915893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_915893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915893 prefixEnd_915893 := by exact prefixLift 915893
  have htrace : WordTrace (prefixWord ++ tailWord_915893) baseStart_915893 baseEnd_915893 := by
    simpa [prefixWord, tailWord_915893, baseEnd_915893] using wordTrace_append hprefix tailTrace_915893
  have hstable : (prefixWord ++ tailWord_915893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915893).length < 2 ^ (prefixWord ++ tailWord_915893).sum := by decide
  have hdescent : baseEnd_915893 < baseStart_915893 := by decide
  rcases family_descends (prefixWord ++ tailWord_915893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915938 : List Nat := [3, 3, 3, 2, 1, 8]
def baseStart_915938 : Nat := 118140960795 + 915938 * 2 ^ 59
def prefixEnd_915938 : Nat := 4983230072969 + 3 ^ 40 * 915938 * 2
def baseEnd_915938 : Nat := 15483668928985765335397

theorem tailTrace_915938 : CollatzResearch.WordTrace tailWord_915938 prefixEnd_915938 15483668928985765335397 := by
  unfold tailWord_915938
  simp only [CollatzResearch.WordTrace]
  refine ⟨8351750838930132650375117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22271335570480353734333645 8351750838930132650375117)
  ·
    refine ⟨3131906564598799743890669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8351750838930132650375117 3131906564598799743890669)
    ·
      refine ⟨1174464961724549903959001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3131906564598799743890669 1174464961724549903959001)
      ·
        refine ⟨880848721293412427969251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1174464961724549903959001 880848721293412427969251)
        ·
          refine ⟨1321273081940118641953877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880848721293412427969251 1321273081940118641953877)
          ·
            refine ⟨15483668928985765335397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1321273081940118641953877 15483668928985765335397)
            ·
              rfl

theorem cell20_915938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 8].length) (baseStart_915938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915938 prefixEnd_915938 := by exact prefixLift 915938
  have htrace : WordTrace (prefixWord ++ tailWord_915938) baseStart_915938 baseEnd_915938 := by
    simpa [prefixWord, tailWord_915938, baseEnd_915938] using wordTrace_append hprefix tailTrace_915938
  have hstable : (prefixWord ++ tailWord_915938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915938).length < 2 ^ (prefixWord ++ tailWord_915938).sum := by decide
  have hdescent : baseEnd_915938 < baseStart_915938 := by decide
  rcases family_descends (prefixWord ++ tailWord_915938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915952 : List Nat := [2, 1, 1, 1, 3, 3, 3, 4, 2]
def baseStart_915952 : Nat := 118140960795 + 915952 * 2 ^ 59
def prefixEnd_915952 : Nat := 4983230072969 + 3 ^ 40 * 915952 * 2
def baseEnd_915952 : Nat := 418065451064093837588995

theorem tailTrace_915952 : CollatzResearch.WordTrace tailWord_915952 prefixEnd_915952 418065451064093837588995 := by
  unfold tailWord_915952
  simp only [CollatzResearch.WordTrace]
  refine ⟨16703756988834905496255055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22271675985113207328340073 16703756988834905496255055)
  ·
    refine ⟨25055635483252358244382583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16703756988834905496255055 25055635483252358244382583)
    ·
      refine ⟨37583453224878537366573875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25055635483252358244382583 37583453224878537366573875)
      ·
        refine ⟨56375179837317806049860813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37583453224878537366573875 56375179837317806049860813)
        ·
          refine ⟨21140692438994177268697805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56375179837317806049860813 21140692438994177268697805)
          ·
            refine ⟨7927759664622816475761677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21140692438994177268697805 7927759664622816475761677)
            ·
              refine ⟨2972909874233556178410629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7927759664622816475761677 2972909874233556178410629)
              ·
                refine ⟨557420601418791783451993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2972909874233556178410629 557420601418791783451993)
                ·
                  refine ⟨418065451064093837588995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557420601418791783451993 418065451064093837588995)
                  ·
                    rfl

theorem cell20_915952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 2].length) (baseStart_915952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915952 prefixEnd_915952 := by exact prefixLift 915952
  have htrace : WordTrace (prefixWord ++ tailWord_915952) baseStart_915952 baseEnd_915952 := by
    simpa [prefixWord, tailWord_915952, baseEnd_915952] using wordTrace_append hprefix tailTrace_915952
  have hstable : (prefixWord ++ tailWord_915952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915952).length < 2 ^ (prefixWord ++ tailWord_915952).sum := by decide
  have hdescent : baseEnd_915952 < baseStart_915952 := by decide
  rcases family_descends (prefixWord ++ tailWord_915952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915987 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 5]
def baseStart_915987 : Nat := 118140960795 + 915987 * 2 ^ 59
def prefixEnd_915987 : Nat := 4983230072969 + 3 ^ 40 * 915987 * 2
def baseEnd_915987 : Nat := 418081426017789271422185

theorem tailTrace_915987 : CollatzResearch.WordTrace tailWord_915987 prefixEnd_915987 418081426017789271422185 := by
  unfold tailWord_915987
  simp only [CollatzResearch.WordTrace]
  refine ⟨33408790532543011970034215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22272527021695341313356143 33408790532543011970034215)
  ·
    refine ⟨50113185798814517955051323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33408790532543011970034215 50113185798814517955051323)
    ·
      refine ⟨75169778698221776932576985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50113185798814517955051323 75169778698221776932576985)
      ·
        refine ⟨56377334023666332699432739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75169778698221776932576985 56377334023666332699432739)
        ·
          refine ⟨84566001035499499049149109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56377334023666332699432739 84566001035499499049149109)
          ·
            refine ⟨7928062597078078035857729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84566001035499499049149109 7928062597078078035857729)
            ·
              refine ⟨5946046947808558526893297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7928062597078078035857729 5946046947808558526893297)
              ·
                refine ⟨4459535210856418895169973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5946046947808558526893297 4459535210856418895169973)
                ·
                  refine ⟨418081426017789271422185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4459535210856418895169973 418081426017789271422185)
                  ·
                    rfl

theorem cell20_915987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_915987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_915987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_915987 prefixEnd_915987 := by exact prefixLift 915987
  have htrace : WordTrace (prefixWord ++ tailWord_915987) baseStart_915987 baseEnd_915987 := by
    simpa [prefixWord, tailWord_915987, baseEnd_915987] using wordTrace_append hprefix tailTrace_915987
  have hstable : (prefixWord ++ tailWord_915987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915987).length < 2 ^ (prefixWord ++ tailWord_915987).sum := by decide
  have hdescent : baseEnd_915987 < baseStart_915987 := by decide
  rcases family_descends (prefixWord ++ tailWord_915987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916000 : List Nat := [2, 1, 1, 6, 2, 2, 1, 2, 3]
def baseStart_916000 : Nat := 118140960795 + 916000 * 2 ^ 59
def prefixEnd_916000 : Nat := 4983230072969 + 3 ^ 40 * 916000 * 2
def baseEnd_916000 : Nat := 418087359572019003988799

theorem tailTrace_916000 : CollatzResearch.WordTrace tailWord_916000 prefixEnd_916000 418087359572019003988799 := by
  unfold tailWord_916000
  simp only [CollatzResearch.WordTrace]
  refine ⟨16704632340747957595128727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22272843120997276793504969 16704632340747957595128727)
  ·
    refine ⟨25056948511121936392693091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16704632340747957595128727 25056948511121936392693091)
    ·
      refine ⟨37585422766682904589039637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25056948511121936392693091 37585422766682904589039637)
      ·
        refine ⟨1761816692188261152611233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37585422766682904589039637 1761816692188261152611233)
        ·
          refine ⟨1321362519141195864458425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1761816692188261152611233 1321362519141195864458425)
          ·
            refine ⟨991021889355896898343819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1321362519141195864458425 991021889355896898343819)
            ·
              refine ⟨1486532834033845347515729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 991021889355896898343819 1486532834033845347515729)
              ·
                refine ⟨1114899625525384010636797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1486532834033845347515729 1114899625525384010636797)
                ·
                  refine ⟨418087359572019003988799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114899625525384010636797 418087359572019003988799)
                  ·
                    rfl

theorem cell20_916000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_916000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916000 prefixEnd_916000 := by exact prefixLift 916000
  have htrace : WordTrace (prefixWord ++ tailWord_916000) baseStart_916000 baseEnd_916000 := by
    simpa [prefixWord, tailWord_916000, baseEnd_916000] using wordTrace_append hprefix tailTrace_916000
  have hstable : (prefixWord ++ tailWord_916000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916000).length < 2 ^ (prefixWord ++ tailWord_916000).sum := by decide
  have hdescent : baseEnd_916000 < baseStart_916000 := by decide
  rcases family_descends (prefixWord ++ tailWord_916000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916021 : List Nat := [1, 3, 3, 1, 1, 2, 5, 1, 3]
def baseStart_916021 : Nat := 118140960795 + 916021 * 2 ^ 59
def prefixEnd_916021 : Nat := 4983230072969 + 3 ^ 40 * 916021 * 2
def baseEnd_916021 : Nat := 418096944544236264288713

theorem tailTrace_916021 : CollatzResearch.WordTrace tailWord_916021 prefixEnd_916021 418096944544236264288713 := by
  unfold tailWord_916021
  simp only [CollatzResearch.WordTrace]
  refine ⟨33410030614419835776771917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22273353742946557184514611 33410030614419835776771917)
  ·
    refine ⟨12528761480407438416289469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33410030614419835776771917 12528761480407438416289469)
    ·
      refine ⟨4698285555152789406108551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12528761480407438416289469 4698285555152789406108551)
      ·
        refine ⟨7047428332729184109162827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4698285555152789406108551 7047428332729184109162827)
        ·
          refine ⟨10571142499093776163744241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7047428332729184109162827 10571142499093776163744241)
          ·
            refine ⟨7928356874320332122808181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10571142499093776163744241 7928356874320332122808181)
            ·
              refine ⟨743283456967531136513267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7928356874320332122808181 743283456967531136513267)
              ·
                refine ⟨1114925185451296704769901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743283456967531136513267 1114925185451296704769901)
                ·
                  refine ⟨418096944544236264288713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114925185451296704769901 418096944544236264288713)
                  ·
                    rfl

theorem cell20_916021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_916021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916021 prefixEnd_916021 := by exact prefixLift 916021
  have htrace : WordTrace (prefixWord ++ tailWord_916021) baseStart_916021 baseEnd_916021 := by
    simpa [prefixWord, tailWord_916021, baseEnd_916021] using wordTrace_append hprefix tailTrace_916021
  have hstable : (prefixWord ++ tailWord_916021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916021).length < 2 ^ (prefixWord ++ tailWord_916021).sum := by decide
  have hdescent : baseEnd_916021 < baseStart_916021 := by decide
  rcases family_descends (prefixWord ++ tailWord_916021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916108 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 8]
def baseStart_916108 : Nat := 118140960795 + 916108 * 2 ^ 59
def prefixEnd_916108 : Nat := 4983230072969 + 3 ^ 40 * 916108 * 2
def baseEnd_916108 : Nat := 418136653714850628388357

theorem tailTrace_916108 : CollatzResearch.WordTrace tailWord_916108 prefixEnd_916108 418136653714850628388357 := by
  unfold tailWord_916108
  simp only [CollatzResearch.WordTrace]
  refine ⟨16706601882552324817594489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22275469176736433090125985 16706601882552324817594489)
  ·
    refine ⟨12529951411914243613195867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16706601882552324817594489 12529951411914243613195867)
    ·
      refine ⟨18794927117871365419793801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12529951411914243613195867 18794927117871365419793801)
      ·
        refine ⟨14096195338403524064845351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18794927117871365419793801 14096195338403524064845351)
        ·
          refine ⟨21144293007605286097268027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14096195338403524064845351 21144293007605286097268027)
          ·
            refine ⟨31716439511407929145902041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21144293007605286097268027 31716439511407929145902041)
            ·
              refine ⟨23787329633555946859426531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31716439511407929145902041 23787329633555946859426531)
              ·
                refine ⟨35680994450333920289139797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23787329633555946859426531 35680994450333920289139797)
                ·
                  refine ⟨418136653714850628388357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35680994450333920289139797 418136653714850628388357)
                  ·
                    rfl

theorem cell20_916108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_916108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916108 prefixEnd_916108 := by exact prefixLift 916108
  have htrace : WordTrace (prefixWord ++ tailWord_916108) baseStart_916108 baseEnd_916108 := by
    simpa [prefixWord, tailWord_916108, baseEnd_916108] using wordTrace_append hprefix tailTrace_916108
  have hstable : (prefixWord ++ tailWord_916108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916108).length < 2 ^ (prefixWord ++ tailWord_916108).sum := by decide
  have hdescent : baseEnd_916108 < baseStart_916108 := by decide
  rcases family_descends (prefixWord ++ tailWord_916108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916128 : List Nat := [2, 1, 1, 4, 5, 1, 1, 5]
def baseStart_916128 : Nat := 118140960795 + 916128 * 2 ^ 59
def prefixEnd_916128 : Nat := 4983230072969 + 3 ^ 40 * 916128 * 2
def baseEnd_916128 : Nat := 139381927419939815907203

theorem tailTrace_916128 : CollatzResearch.WordTrace tailWord_916128 prefixEnd_916128 139381927419939815907203 := by
  unfold tailWord_916128
  simp only [CollatzResearch.WordTrace]
  refine ⟨16706966612516096525458519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22275955483354795367278025 16706966612516096525458519)
  ·
    refine ⟨25060449918774144788187779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16706966612516096525458519 25060449918774144788187779)
    ·
      refine ⟨37590674878161217182281669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25060449918774144788187779 37590674878161217182281669)
      ·
        refine ⟨7048251539655228221677813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37590674878161217182281669 7048251539655228221677813)
        ·
          refine ⟨660773581842677645782295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7048251539655228221677813 660773581842677645782295)
          ·
            refine ⟨991160372764016468673443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660773581842677645782295 991160372764016468673443)
            ·
              refine ⟨1486740559146024703010165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 991160372764016468673443 1486740559146024703010165)
              ·
                refine ⟨139381927419939815907203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1486740559146024703010165 139381927419939815907203)
                ·
                  rfl

theorem cell20_916128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 5].length) (baseStart_916128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916128 prefixEnd_916128 := by exact prefixLift 916128
  have htrace : WordTrace (prefixWord ++ tailWord_916128) baseStart_916128 baseEnd_916128 := by
    simpa [prefixWord, tailWord_916128, baseEnd_916128] using wordTrace_append hprefix tailTrace_916128
  have hstable : (prefixWord ++ tailWord_916128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916128).length < 2 ^ (prefixWord ++ tailWord_916128).sum := by decide
  have hdescent : baseEnd_916128 < baseStart_916128 := by decide
  rcases family_descends (prefixWord ++ tailWord_916128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916142 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_916142 : Nat := 118140960795 + 916142 * 2 ^ 59
def prefixEnd_916142 : Nat := 4983230072969 + 3 ^ 40 * 916142 * 2
def baseEnd_916142 : Nat := 418152172241297621254885

theorem tailTrace_916142 : CollatzResearch.WordTrace tailWord_916142 prefixEnd_916142 418152172241297621254885 := by
  unfold tailWord_916142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4176805480872684180240835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22276295897987648961284453 4176805480872684180240835)
  ·
    refine ⟨6265208221309026270361253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4176805480872684180240835 6265208221309026270361253)
    ·
      refine ⟨1174726541495442425692735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6265208221309026270361253 1174726541495442425692735)
      ·
        refine ⟨1762089812243163638539103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1174726541495442425692735 1762089812243163638539103)
        ·
          refine ⟨2643134718364745457808655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762089812243163638539103 2643134718364745457808655)
          ·
            refine ⟨3964702077547118186712983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2643134718364745457808655 3964702077547118186712983)
            ·
              refine ⟨5947053116320677280069475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964702077547118186712983 5947053116320677280069475)
              ·
                refine ⟨8920579674481015920104213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5947053116320677280069475 8920579674481015920104213)
                ·
                  refine ⟨418152172241297621254885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8920579674481015920104213 418152172241297621254885)
                  ·
                    rfl

theorem cell20_916142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_916142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916142 prefixEnd_916142 := by exact prefixLift 916142
  have htrace : WordTrace (prefixWord ++ tailWord_916142) baseStart_916142 baseEnd_916142 := by
    simpa [prefixWord, tailWord_916142, baseEnd_916142] using wordTrace_append hprefix tailTrace_916142
  have hstable : (prefixWord ++ tailWord_916142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916142).length < 2 ^ (prefixWord ++ tailWord_916142).sum := by decide
  have hdescent : baseEnd_916142 < baseStart_916142 := by decide
  rcases family_descends (prefixWord ++ tailWord_916142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916170 : List Nat := [3, 1, 2, 1, 4, 2, 7]
def baseStart_916170 : Nat := 118140960795 + 916170 * 2 ^ 59
def prefixEnd_916170 : Nat := 4983230072969 + 3 ^ 40 * 916170 * 2
def baseEnd_916170 : Nat := 46462772467139329813493

theorem tailTrace_916170 : CollatzResearch.WordTrace tailWord_916170 prefixEnd_916170 46462772467139329813493 := by
  unfold tailWord_916170
  simp only [CollatzResearch.WordTrace]
  refine ⟨8353866272720008555986491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22276976727253356149297309 8353866272720008555986491)
  ·
    refine ⟨12530799409080012833979737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8353866272720008555986491 12530799409080012833979737)
    ·
      refine ⟨9398099556810009625484803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12530799409080012833979737 9398099556810009625484803)
      ·
        refine ⟨14097149335215014438227205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9398099556810009625484803 14097149335215014438227205)
        ·
          refine ⟨2643215500352815207167601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14097149335215014438227205 2643215500352815207167601)
          ·
            refine ⟨1982411625264611405375701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2643215500352815207167601 1982411625264611405375701)
            ·
              refine ⟨46462772467139329813493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1982411625264611405375701 46462772467139329813493)
              ·
                rfl

theorem cell20_916170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 7].length) (baseStart_916170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916170 prefixEnd_916170 := by exact prefixLift 916170
  have htrace : WordTrace (prefixWord ++ tailWord_916170) baseStart_916170 baseEnd_916170 := by
    simpa [prefixWord, tailWord_916170, baseEnd_916170] using wordTrace_append hprefix tailTrace_916170
  have hstable : (prefixWord ++ tailWord_916170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916170).length < 2 ^ (prefixWord ++ tailWord_916170).sum := by decide
  have hdescent : baseEnd_916170 < baseStart_916170 := by decide
  rcases family_descends (prefixWord ++ tailWord_916170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916177 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 5]
def baseStart_916177 : Nat := 118140960795 + 916177 * 2 ^ 59
def prefixEnd_916177 : Nat := 4983230072969 + 3 ^ 40 * 916177 * 2
def baseEnd_916177 : Nat := 418168147194993055088075

theorem tailTrace_916177 : CollatzResearch.WordTrace tailWord_916177 prefixEnd_916177 418168147194993055088075 := by
  unfold tailWord_916177
  simp only [CollatzResearch.WordTrace]
  refine ⟨33415720401854674419450785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22277146934569782946300523 33415720401854674419450785)
  ·
    refine ⟨25061790301391005814588089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33415720401854674419450785 25061790301391005814588089)
    ·
      refine ⟨18796342726043254360941067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25061790301391005814588089 18796342726043254360941067)
      ·
        refine ⟨28194514089064881541411601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18796342726043254360941067 28194514089064881541411601)
        ·
          refine ⟨21145885566798661156058701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28194514089064881541411601 21145885566798661156058701)
          ·
            refine ⟨7929707087549497933522013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21145885566798661156058701 7929707087549497933522013)
            ·
              refine ⟨2973640157831061725070755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7929707087549497933522013 2973640157831061725070755)
              ·
                refine ⟨4460460236746592587606133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2973640157831061725070755 4460460236746592587606133)
                ·
                  refine ⟨418168147194993055088075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4460460236746592587606133 418168147194993055088075)
                  ·
                    rfl

theorem cell20_916177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_916177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916177 prefixEnd_916177 := by exact prefixLift 916177
  have htrace : WordTrace (prefixWord ++ tailWord_916177) baseStart_916177 baseEnd_916177 := by
    simpa [prefixWord, tailWord_916177, baseEnd_916177] using wordTrace_append hprefix tailTrace_916177
  have hstable : (prefixWord ++ tailWord_916177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916177).length < 2 ^ (prefixWord ++ tailWord_916177).sum := by decide
  have hdescent : baseEnd_916177 < baseStart_916177 := by decide
  rcases family_descends (prefixWord ++ tailWord_916177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916218 : List Nat := [3, 1, 1, 1, 1, 3, 5, 3, 2]
def baseStart_916218 : Nat := 118140960795 + 916218 * 2 ^ 59
def prefixEnd_916218 : Nat := 4983230072969 + 3 ^ 40 * 916218 * 2
def baseEnd_916218 : Nat := 418186860712179134721241

theorem tailTrace_916218 : CollatzResearch.WordTrace tailWord_916218 prefixEnd_916218 418186860712179134721241 := by
  unfold tailWord_916218
  simp only [CollatzResearch.WordTrace]
  refine ⟨8354303948676534605423327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22278143863137425614462205 8354303948676534605423327)
  ·
    refine ⟨12531455923014801908134991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8354303948676534605423327 12531455923014801908134991)
    ·
      refine ⟨18797183884522202862202487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12531455923014801908134991 18797183884522202862202487)
      ·
        refine ⟨28195775826783304293303731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18797183884522202862202487 28195775826783304293303731)
        ·
          refine ⟨42293663740174956439955597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28195775826783304293303731 42293663740174956439955597)
          ·
            refine ⟨15860123902565608664983349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42293663740174956439955597 15860123902565608664983349)
            ·
              refine ⟨1486886615865525812342189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15860123902565608664983349 1486886615865525812342189)
              ·
                refine ⟨557582480949572179628321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1486886615865525812342189 557582480949572179628321)
                ·
                  refine ⟨418186860712179134721241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557582480949572179628321 418186860712179134721241)
                  ·
                    rfl

theorem cell20_916218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_916218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916218 prefixEnd_916218 := by exact prefixLift 916218
  have htrace : WordTrace (prefixWord ++ tailWord_916218) baseStart_916218 baseEnd_916218 := by
    simpa [prefixWord, tailWord_916218, baseEnd_916218] using wordTrace_append hprefix tailTrace_916218
  have hstable : (prefixWord ++ tailWord_916218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916218).length < 2 ^ (prefixWord ++ tailWord_916218).sum := by decide
  have hdescent : baseEnd_916218 < baseStart_916218 := by decide
  rcases family_descends (prefixWord ++ tailWord_916218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916242 : List Nat := [3, 2, 4, 1, 2, 1, 2, 5]
def baseStart_916242 : Nat := 118140960795 + 916242 * 2 ^ 59
def prefixEnd_916242 : Nat := 4983230072969 + 3 ^ 40 * 916242 * 2
def baseEnd_916242 : Nat := 139399271655380572640381

theorem tailTrace_916242 : CollatzResearch.WordTrace tailWord_916242 prefixEnd_916242 139399271655380572640381 := by
  unfold tailWord_916242
  simp only [CollatzResearch.WordTrace]
  refine ⟨8354522786654797630141745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22278727431079460347044653 8354522786654797630141745)
  ·
    refine ⟨6265892089991098222606309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8354522786654797630141745 6265892089991098222606309)
    ·
      refine ⟨1174854766873330916738683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6265892089991098222606309 1174854766873330916738683)
      ·
        refine ⟨1762282150309996375108025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1174854766873330916738683 1762282150309996375108025)
        ·
          refine ⟨1321711612732497281331019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1762282150309996375108025 1321711612732497281331019)
          ·
            refine ⟨1982567419098745921996529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1321711612732497281331019 1982567419098745921996529)
            ·
              refine ⟨1486925564324059441497397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1982567419098745921996529 1486925564324059441497397)
              ·
                refine ⟨139399271655380572640381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1486925564324059441497397 139399271655380572640381)
                ·
                  rfl

theorem cell20_916242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_916242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916242 prefixEnd_916242 := by exact prefixLift 916242
  have htrace : WordTrace (prefixWord ++ tailWord_916242) baseStart_916242 baseEnd_916242 := by
    simpa [prefixWord, tailWord_916242, baseEnd_916242] using wordTrace_append hprefix tailTrace_916242
  have hstable : (prefixWord ++ tailWord_916242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916242).length < 2 ^ (prefixWord ++ tailWord_916242).sum := by decide
  have hdescent : baseEnd_916242 < baseStart_916242 := by decide
  rcases family_descends (prefixWord ++ tailWord_916242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916332 : List Nat := [2, 2, 1, 1, 4, 1, 4, 3, 2]
def baseStart_916332 : Nat := 118140960795 + 916332 * 2 ^ 59
def prefixEnd_916332 : Nat := 4983230072969 + 3 ^ 40 * 916332 * 2
def baseEnd_916332 : Nat := 418238893418501404920775

theorem tailTrace_916332 : CollatzResearch.WordTrace tailWord_916332 prefixEnd_916332 418238893418501404920775 := by
  unfold tailWord_916332
  simp only [CollatzResearch.WordTrace]
  refine ⟨16710686858146567945671625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22280915810862090594228833 16710686858146567945671625)
  ·
    refine ⟨12533015143609925959253719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16710686858146567945671625 12533015143609925959253719)
    ·
      refine ⟨18799522715414888938880579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12533015143609925959253719 18799522715414888938880579)
      ·
        refine ⟨28199284073122333408320869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18799522715414888938880579 28199284073122333408320869)
        ·
          refine ⟨5287365763710437514060163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28199284073122333408320869 5287365763710437514060163)
          ·
            refine ⟨7931048645565656271090245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5287365763710437514060163 7931048645565656271090245)
            ·
              refine ⟨1487071621043560550829421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7931048645565656271090245 1487071621043560550829421)
              ·
                refine ⟨557651857891335206561033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1487071621043560550829421 557651857891335206561033)
                ·
                  refine ⟨418238893418501404920775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557651857891335206561033 418238893418501404920775)
                  ·
                    rfl

theorem cell20_916332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_916332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916332 prefixEnd_916332 := by exact prefixLift 916332
  have htrace : WordTrace (prefixWord ++ tailWord_916332) baseStart_916332 baseEnd_916332 := by
    simpa [prefixWord, tailWord_916332, baseEnd_916332] using wordTrace_append hprefix tailTrace_916332
  have hstable : (prefixWord ++ tailWord_916332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916332).length < 2 ^ (prefixWord ++ tailWord_916332).sum := by decide
  have hdescent : baseEnd_916332 < baseStart_916332 := by decide
  rcases family_descends (prefixWord ++ tailWord_916332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916342 : List Nat := [5, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_916342 : Nat := 118140960795 + 916342 * 2 ^ 59
def prefixEnd_916342 : Nat := 4983230072969 + 3 ^ 40 * 916342 * 2
def baseEnd_916342 : Nat := 418243457690985814587401

theorem tailTrace_916342 : CollatzResearch.WordTrace tailWord_916342 prefixEnd_916342 418243457690985814587401 := by
  unfold tailWord_916342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2088858652891056724950455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22281158964171271732804853 2088858652891056724950455)
  ·
    refine ⟨3133287979336585087425683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2088858652891056724950455 3133287979336585087425683)
    ·
      refine ⟨4699931969004877631138525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3133287979336585087425683 4699931969004877631138525)
      ·
        refine ⟨1762474488376829111676947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4699931969004877631138525 1762474488376829111676947)
        ·
          refine ⟨2643711732565243667515421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762474488376829111676947 2643711732565243667515421)
          ·
            refine ⟨991391899711966375318283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2643711732565243667515421 991391899711966375318283)
            ·
              refine ⟨1487087849567949562977425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 991391899711966375318283 1487087849567949562977425)
              ·
                refine ⟨1115315887175962172233069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1487087849567949562977425 1115315887175962172233069)
                ·
                  refine ⟨418243457690985814587401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1115315887175962172233069 418243457690985814587401)
                  ·
                    rfl

theorem cell20_916342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_916342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916342 prefixEnd_916342 := by exact prefixLift 916342
  have htrace : WordTrace (prefixWord ++ tailWord_916342) baseStart_916342 baseEnd_916342 := by
    simpa [prefixWord, tailWord_916342, baseEnd_916342] using wordTrace_append hprefix tailTrace_916342
  have hstable : (prefixWord ++ tailWord_916342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916342).length < 2 ^ (prefixWord ++ tailWord_916342).sum := by decide
  have hdescent : baseEnd_916342 < baseStart_916342 := by decide
  rcases family_descends (prefixWord ++ tailWord_916342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916405 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 5]
def baseStart_916405 : Nat := 118140960795 + 916405 * 2 ^ 59
def prefixEnd_916405 : Nat := 4983230072969 + 3 ^ 40 * 916405 * 2
def baseEnd_916405 : Nat := 418272212607637595487143

theorem tailTrace_916405 : CollatzResearch.WordTrace tailWord_916405 prefixEnd_916405 418272212607637595487143 := by
  unfold tailWord_916405
  simp only [CollatzResearch.WordTrace]
  refine ⟨33424036245028669358750669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22282690830019112905833779 33424036245028669358750669)
  ·
    refine ⟨12534013591885751009531501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33424036245028669358750669 12534013591885751009531501)
    ·
      refine ⟨4700255096957156628574313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12534013591885751009531501 4700255096957156628574313)
      ·
        refine ⟨3525191322717867471430735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4700255096957156628574313 3525191322717867471430735)
        ·
          refine ⟨5287786984076801207146103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3525191322717867471430735 5287786984076801207146103)
          ·
            refine ⟨7931680476115201810719155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5287786984076801207146103 7931680476115201810719155)
            ·
              refine ⟨11897520714172802716078733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7931680476115201810719155 11897520714172802716078733)
              ·
                refine ⟨4461570267814801018529525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11897520714172802716078733 4461570267814801018529525)
                ·
                  refine ⟨418272212607637595487143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4461570267814801018529525 418272212607637595487143)
                  ·
                    rfl

theorem cell20_916405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_916405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916405 prefixEnd_916405 := by exact prefixLift 916405
  have htrace : WordTrace (prefixWord ++ tailWord_916405) baseStart_916405 baseEnd_916405 := by
    simpa [prefixWord, tailWord_916405, baseEnd_916405] using wordTrace_append hprefix tailTrace_916405
  have hstable : (prefixWord ++ tailWord_916405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916405).length < 2 ^ (prefixWord ++ tailWord_916405).sum := by decide
  have hdescent : baseEnd_916405 < baseStart_916405 := by decide
  rcases family_descends (prefixWord ++ tailWord_916405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916436 : List Nat := [2, 4, 1, 2, 1, 2, 2, 6]
def baseStart_916436 : Nat := 118140960795 + 916436 * 2 ^ 59
def prefixEnd_916436 : Nat := 4983230072969 + 3 ^ 40 * 916436 * 2
def baseEnd_916436 : Nat := 139428787284113088484561

theorem tailTrace_916436 : CollatzResearch.WordTrace tailWord_916436 prefixEnd_916436 139428787284113088484561 := by
  unfold tailWord_916436
  simp only [CollatzResearch.WordTrace]
  refine ⟨16712583453958180826564581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22283444605277574435419441 16712583453958180826564581)
  ·
    refine ⟨3133609397617158904980859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16712583453958180826564581 3133609397617158904980859)
    ·
      refine ⟨4700414096425738357471289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3133609397617158904980859 4700414096425738357471289)
      ·
        refine ⟨3525310572319303768103467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4700414096425738357471289 3525310572319303768103467)
        ·
          refine ⟨5287965858478955652155201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3525310572319303768103467 5287965858478955652155201)
          ·
            refine ⟨3965974393859216739116401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5287965858478955652155201 3965974393859216739116401)
            ·
              refine ⟨2974480795394412554337301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3965974393859216739116401 2974480795394412554337301)
              ·
                refine ⟨139428787284113088484561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2974480795394412554337301 139428787284113088484561)
                ·
                  rfl

theorem cell20_916436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_916436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916436 prefixEnd_916436 := by exact prefixLift 916436
  have htrace : WordTrace (prefixWord ++ tailWord_916436) baseStart_916436 baseEnd_916436 := by
    simpa [prefixWord, tailWord_916436, baseEnd_916436] using wordTrace_append hprefix tailTrace_916436
  have hstable : (prefixWord ++ tailWord_916436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916436).length < 2 ^ (prefixWord ++ tailWord_916436).sum := by decide
  have hdescent : baseEnd_916436 < baseStart_916436 := by decide
  rcases family_descends (prefixWord ++ tailWord_916436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916453 : List Nat := [1, 3, 1, 6, 2, 7]
def baseStart_916453 : Nat := 118140960795 + 916453 * 2 ^ 59
def prefixEnd_916453 : Nat := 4983230072969 + 3 ^ 40 * 916453 * 2
def baseEnd_916453 : Nat := 15492374856131954143961

theorem tailTrace_916453 : CollatzResearch.WordTrace tailWord_916453 prefixEnd_916453 15492374856131954143961 := by
  unfold tailWord_916453
  simp only [CollatzResearch.WordTrace]
  refine ⟨33425786948854773556498013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22283857965903182370998675 33425786948854773556498013)
  ·
    refine ⟨12534670105820540083686755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33425786948854773556498013 12534670105820540083686755)
    ·
      refine ⟨18802005158730810125530133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12534670105820540083686755 18802005158730810125530133)
      ·
        refine ⟨881343991815506724634225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18802005158730810125530133 881343991815506724634225)
        ·
          refine ⟨661007993861630043475669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 881343991815506724634225 661007993861630043475669)
          ·
            refine ⟨15492374856131954143961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 661007993861630043475669 15492374856131954143961)
            ·
              rfl

theorem cell20_916453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 7].length) (baseStart_916453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916453 prefixEnd_916453 := by exact prefixLift 916453
  have htrace : WordTrace (prefixWord ++ tailWord_916453) baseStart_916453 baseEnd_916453 := by
    simpa [prefixWord, tailWord_916453, baseEnd_916453] using wordTrace_append hprefix tailTrace_916453
  have hstable : (prefixWord ++ tailWord_916453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916453).length < 2 ^ (prefixWord ++ tailWord_916453).sum := by decide
  have hdescent : baseEnd_916453 < baseStart_916453 := by decide
  rcases family_descends (prefixWord ++ tailWord_916453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916463 : List Nat := [1, 1, 2, 1, 4, 5, 2, 2, 2]
def baseStart_916463 : Nat := 118140960795 + 916463 * 2 ^ 59
def prefixEnd_916463 : Nat := 4983230072969 + 3 ^ 40 * 916463 * 2
def baseEnd_916463 : Nat := 418298685388047171553573

theorem tailTrace_916463 : CollatzResearch.WordTrace tailWord_916463 prefixEnd_916463 418298685388047171553573 := by
  unfold tailWord_916463
  simp only [CollatzResearch.WordTrace]
  refine ⟨33426151678818545264362043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22284101119212363509574695 33426151678818545264362043)
  ·
    refine ⟨50139227518227817896543065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33426151678818545264362043 50139227518227817896543065)
    ·
      refine ⟨37604420638670863422407299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50139227518227817896543065 37604420638670863422407299)
      ·
        refine ⟨56406630958006295133610949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37604420638670863422407299 56406630958006295133610949)
        ·
          refine ⟨10576243304626180337552053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56406630958006295133610949 10576243304626180337552053)
          ·
            refine ⟨991522809808704406645505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10576243304626180337552053 991522809808704406645505)
            ·
              refine ⟨743642107356528304984129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 991522809808704406645505 743642107356528304984129)
              ·
                refine ⟨557731580517396228738097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 743642107356528304984129 557731580517396228738097)
                ·
                  refine ⟨418298685388047171553573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557731580517396228738097 418298685388047171553573)
                  ·
                    rfl

theorem cell20_916463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 2].length) (baseStart_916463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916463 prefixEnd_916463 := by exact prefixLift 916463
  have htrace : WordTrace (prefixWord ++ tailWord_916463) baseStart_916463 baseEnd_916463 := by
    simpa [prefixWord, tailWord_916463, baseEnd_916463] using wordTrace_append hprefix tailTrace_916463
  have hstable : (prefixWord ++ tailWord_916463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916463).length < 2 ^ (prefixWord ++ tailWord_916463).sum := by decide
  have hdescent : baseEnd_916463 < baseStart_916463 := by decide
  rcases family_descends (prefixWord ++ tailWord_916463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916488 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 6]
def baseStart_916488 : Nat := 118140960795 + 916488 * 2 ^ 59
def prefixEnd_916488 : Nat := 4983230072969 + 3 ^ 40 * 916488 * 2
def baseEnd_916488 : Nat := 418310096069258195720137

theorem tailTrace_916488 : CollatzResearch.WordTrace tailWord_916488 prefixEnd_916488 418310096069258195720137 := by
  unfold tailWord_916488
  simp only [CollatzResearch.WordTrace]
  refine ⟨16713531751863987267011059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22284709002485316356014745 16713531751863987267011059)
  ·
    refine ⟨25070297627795980900516589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16713531751863987267011059 25070297627795980900516589)
    ·
      refine ⟨9401361610423492837693721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25070297627795980900516589 9401361610423492837693721)
      ·
        refine ⟨7051021207817619628270291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9401361610423492837693721 7051021207817619628270291)
        ·
          refine ⟨10576531811726429442405437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7051021207817619628270291 10576531811726429442405437)
          ·
            refine ⟨3966199429397411040902039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10576531811726429442405437 3966199429397411040902039)
            ·
              refine ⟨5949299144096116561353059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3966199429397411040902039 5949299144096116561353059)
              ·
                refine ⟨8923948716144174842029589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5949299144096116561353059 8923948716144174842029589)
                ·
                  refine ⟨418310096069258195720137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8923948716144174842029589 418310096069258195720137)
                  ·
                    rfl

theorem cell20_916488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_916488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916488 prefixEnd_916488 := by exact prefixLift 916488
  have htrace : WordTrace (prefixWord ++ tailWord_916488) baseStart_916488 baseEnd_916488 := by
    simpa [prefixWord, tailWord_916488, baseEnd_916488] using wordTrace_append hprefix tailTrace_916488
  have hstable : (prefixWord ++ tailWord_916488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916488).length < 2 ^ (prefixWord ++ tailWord_916488).sum := by decide
  have hdescent : baseEnd_916488 < baseStart_916488 := by decide
  rcases family_descends (prefixWord ++ tailWord_916488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916505 : List Nat := [1, 2, 1, 2, 1, 1, 5, 5, 2]
def baseStart_916505 : Nat := 118140960795 + 916505 * 2 ^ 59
def prefixEnd_916505 : Nat := 4983230072969 + 3 ^ 40 * 916505 * 2
def baseEnd_916505 : Nat := 418317855332481692153401

theorem tailTrace_916505 : CollatzResearch.WordTrace tailWord_916505 prefixEnd_916505 418317855332481692153401 := by
  unfold tailWord_916505
  simp only [CollatzResearch.WordTrace]
  refine ⟨33427683544666386437390969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22285122363110924291593979 33427683544666386437390969)
  ·
    refine ⟨25070762658499789828043227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33427683544666386437390969 25070762658499789828043227)
    ·
      refine ⟨37606143987749684742064841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25070762658499789828043227 37606143987749684742064841)
      ·
        refine ⟨28204607990812263556548631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37606143987749684742064841 28204607990812263556548631)
        ·
          refine ⟨42306911986218395334822947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28204607990812263556548631 42306911986218395334822947)
          ·
            refine ⟨63460367979327593002234421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42306911986218395334822947 63460367979327593002234421)
            ·
              refine ⟨5949409498061961843959477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63460367979327593002234421 5949409498061961843959477)
              ·
                refine ⟨557757140443308922871201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5949409498061961843959477 557757140443308922871201)
                ·
                  refine ⟨418317855332481692153401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557757140443308922871201 418317855332481692153401)
                  ·
                    rfl

theorem cell20_916505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 2].length) (baseStart_916505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916505 prefixEnd_916505 := by exact prefixLift 916505
  have htrace : WordTrace (prefixWord ++ tailWord_916505) baseStart_916505 baseEnd_916505 := by
    simpa [prefixWord, tailWord_916505, baseEnd_916505] using wordTrace_append hprefix tailTrace_916505
  have hstable : (prefixWord ++ tailWord_916505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916505).length < 2 ^ (prefixWord ++ tailWord_916505).sum := by decide
  have hdescent : baseEnd_916505 < baseStart_916505 := by decide
  rcases family_descends (prefixWord ++ tailWord_916505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916522 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 4]
def baseStart_916522 : Nat := 118140960795 + 916522 * 2 ^ 59
def prefixEnd_916522 : Nat := 4983230072969 + 3 ^ 40 * 916522 * 2
def baseEnd_916522 : Nat := 418325614595705188586665

theorem tailTrace_916522 : CollatzResearch.WordTrace tailWord_916522 prefixEnd_916522 418325614595705188586665 := by
  unfold tailWord_916522
  simp only [CollatzResearch.WordTrace]
  refine ⟨8357075896401199585189955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22285535723736532227173213 8357075896401199585189955)
  ·
    refine ⟨12535613844601799377784933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8357075896401199585189955 12535613844601799377784933)
    ·
      refine ⟨2350427595862837383334675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12535613844601799377784933 2350427595862837383334675)
      ·
        refine ⟨3525641393794256075002013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2350427595862837383334675 3525641393794256075002013)
        ·
          refine ⟨1322115522672846028125755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3525641393794256075002013 1322115522672846028125755)
          ·
            refine ⟨1983173284009269042188633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322115522672846028125755 1983173284009269042188633)
            ·
              refine ⟨1487379963006951781641475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1983173284009269042188633 1487379963006951781641475)
              ·
                refine ⟨2231069944510427672462213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1487379963006951781641475 2231069944510427672462213)
                ·
                  refine ⟨418325614595705188586665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2231069944510427672462213 418325614595705188586665)
                  ·
                    rfl

theorem cell20_916522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_916522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916522 prefixEnd_916522 := by exact prefixLift 916522
  have htrace : WordTrace (prefixWord ++ tailWord_916522) baseStart_916522 baseEnd_916522 := by
    simpa [prefixWord, tailWord_916522, baseEnd_916522] using wordTrace_append hprefix tailTrace_916522
  have hstable : (prefixWord ++ tailWord_916522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916522).length < 2 ^ (prefixWord ++ tailWord_916522).sum := by decide
  have hdescent : baseEnd_916522 < baseStart_916522 := by decide
  rcases family_descends (prefixWord ++ tailWord_916522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916532 : List Nat := [2, 5, 1, 2, 1, 2, 3, 1, 3]
def baseStart_916532 : Nat := 118140960795 + 916532 * 2 ^ 59
def prefixEnd_916532 : Nat := 4983230072969 + 3 ^ 40 * 916532 * 2
def baseEnd_916532 : Nat := 418330178868189598253291

theorem tailTrace_916532 : CollatzResearch.WordTrace tailWord_916532 prefixEnd_916532 418330178868189598253291 := by
  unfold tailWord_916532
  simp only [CollatzResearch.WordTrace]
  refine ⟨16714334157784285024311925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22285778877045713365749233 16714334157784285024311925)
  ·
    refine ⟨1566968827292276721029243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16714334157784285024311925 1566968827292276721029243)
    ·
      refine ⟨2350453240938415081543865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1566968827292276721029243 2350453240938415081543865)
      ·
        refine ⟨1762839930703811311157899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2350453240938415081543865 1762839930703811311157899)
        ·
          refine ⟨2644259896055716966736849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762839930703811311157899 2644259896055716966736849)
          ·
            refine ⟨1983194922041787725052637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2644259896055716966736849 1983194922041787725052637)
            ·
              refine ⟨743698095765670396894739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1983194922041787725052637 743698095765670396894739)
              ·
                refine ⟨1115547143648505595342109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743698095765670396894739 1115547143648505595342109)
                ·
                  refine ⟨418330178868189598253291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1115547143648505595342109 418330178868189598253291)
                  ·
                    rfl

theorem cell20_916532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_916532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916532 prefixEnd_916532 := by exact prefixLift 916532
  have htrace : WordTrace (prefixWord ++ tailWord_916532) baseStart_916532 baseEnd_916532 := by
    simpa [prefixWord, tailWord_916532, baseEnd_916532] using wordTrace_append hprefix tailTrace_916532
  have hstable : (prefixWord ++ tailWord_916532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916532).length < 2 ^ (prefixWord ++ tailWord_916532).sum := by decide
  have hdescent : baseEnd_916532 < baseStart_916532 := by decide
  rcases family_descends (prefixWord ++ tailWord_916532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916533 : List Nat := [1, 3, 3, 1, 1, 1, 1, 9]
def baseStart_916533 : Nat := 118140960795 + 916533 * 2 ^ 59
def prefixEnd_916533 : Nat := 4983230072969 + 3 ^ 40 * 916533 * 2
def baseEnd_916533 : Nat := 139443545098479346406651

theorem tailTrace_916533 : CollatzResearch.WordTrace tailWord_916533 prefixEnd_916533 139443545098479346406651 := by
  unfold tailWord_916533
  simp only [CollatzResearch.WordTrace]
  refine ⟨33428704788564947219410253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22285803192376631479606835 33428704788564947219410253)
  ·
    refine ⟨12535764295711855207278845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33428704788564947219410253 12535764295711855207278845)
    ·
      refine ⟨4700911610891945702729567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12535764295711855207278845 4700911610891945702729567)
      ·
        refine ⟨7051367416337918554094351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4700911610891945702729567 7051367416337918554094351)
        ·
          refine ⟨10577051124506877831141527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7051367416337918554094351 10577051124506877831141527)
          ·
            refine ⟨15865576686760316746712291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10577051124506877831141527 15865576686760316746712291)
            ·
              refine ⟨23798365030140475120068437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15865576686760316746712291 23798365030140475120068437)
              ·
                refine ⟨139443545098479346406651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23798365030140475120068437 139443545098479346406651)
                ·
                  rfl

theorem cell20_916533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 9].length) (baseStart_916533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916533 prefixEnd_916533 := by exact prefixLift 916533
  have htrace : WordTrace (prefixWord ++ tailWord_916533) baseStart_916533 baseEnd_916533 := by
    simpa [prefixWord, tailWord_916533, baseEnd_916533] using wordTrace_append hprefix tailTrace_916533
  have hstable : (prefixWord ++ tailWord_916533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916533).length < 2 ^ (prefixWord ++ tailWord_916533).sum := by decide
  have hdescent : baseEnd_916533 < baseStart_916533 := by decide
  rcases family_descends (prefixWord ++ tailWord_916533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916564 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 6]
def baseStart_916564 : Nat := 118140960795 + 916564 * 2 ^ 59
def prefixEnd_916564 : Nat := 4983230072969 + 3 ^ 40 * 916564 * 2
def baseEnd_916564 : Nat := 418344784540139709186493

theorem tailTrace_916564 : CollatzResearch.WordTrace tailWord_916564 prefixEnd_916564 418344784540139709186493 := by
  unfold tailWord_916564
  simp only [CollatzResearch.WordTrace]
  refine ⟨16714917725726319756894373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22286556967635093009192497 16714917725726319756894373)
  ·
    refine ⟨3134047073573684954417695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16714917725726319756894373 3134047073573684954417695)
    ·
      refine ⟨4701070610360527431626543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3134047073573684954417695 4701070610360527431626543)
      ·
        refine ⟨7051605915540791147439815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4701070610360527431626543 7051605915540791147439815)
        ·
          refine ⟨10577408873311186721159723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7051605915540791147439815 10577408873311186721159723)
          ·
            refine ⟨15866113309966780081739585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10577408873311186721159723 15866113309966780081739585)
            ·
              refine ⟨11899584982475085061304689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15866113309966780081739585 11899584982475085061304689)
              ·
                refine ⟨8924688736856313795978517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11899584982475085061304689 8924688736856313795978517)
                ·
                  refine ⟨418344784540139709186493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8924688736856313795978517 418344784540139709186493)
                  ·
                    rfl

theorem cell20_916564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_916564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916564 prefixEnd_916564 := by exact prefixLift 916564
  have htrace : WordTrace (prefixWord ++ tailWord_916564) baseStart_916564 baseEnd_916564 := by
    simpa [prefixWord, tailWord_916564, baseEnd_916564] using wordTrace_append hprefix tailTrace_916564
  have hstable : (prefixWord ++ tailWord_916564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916564).length < 2 ^ (prefixWord ++ tailWord_916564).sum := by decide
  have hdescent : baseEnd_916564 < baseStart_916564 := by decide
  rcases family_descends (prefixWord ++ tailWord_916564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916636 : List Nat := [2, 2, 3, 2, 1, 3, 1, 4, 2]
def baseStart_916636 : Nat := 118140960795 + 916636 * 2 ^ 59
def prefixEnd_916636 : Nat := 4983230072969 + 3 ^ 40 * 916636 * 2
def baseEnd_916636 : Nat := 418377647302027458786199

theorem tailTrace_916636 : CollatzResearch.WordTrace tailWord_916636 prefixEnd_916636 418377647302027458786199 := by
  unfold tailWord_916636
  simp only [CollatzResearch.WordTrace]
  refine ⟨16716230753595897905204881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22288307671461197206939841 16716230753595897905204881)
  ·
    refine ⟨12537173065196923428903661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16716230753595897905204881 12537173065196923428903661)
    ·
      refine ⟨4701439899448846285838873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12537173065196923428903661 4701439899448846285838873)
      ·
        refine ⟨3526079924586634714379155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4701439899448846285838873 3526079924586634714379155)
        ·
          refine ⟨5289119886879952071568733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3526079924586634714379155 5289119886879952071568733)
          ·
            refine ⟨1983419957579982026838275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5289119886879952071568733 1983419957579982026838275)
            ·
              refine ⟨2975129936369973040257413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983419957579982026838275 2975129936369973040257413)
              ·
                refine ⟨557836863069369945048265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2975129936369973040257413 557836863069369945048265)
                ·
                  refine ⟨418377647302027458786199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557836863069369945048265 418377647302027458786199)
                  ·
                    rfl

theorem cell20_916636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_916636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916636 prefixEnd_916636 := by exact prefixLift 916636
  have htrace : WordTrace (prefixWord ++ tailWord_916636) baseStart_916636 baseEnd_916636 := by
    simpa [prefixWord, tailWord_916636, baseEnd_916636] using wordTrace_append hprefix tailTrace_916636
  have hstable : (prefixWord ++ tailWord_916636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916636).length < 2 ^ (prefixWord ++ tailWord_916636).sum := by decide
  have hdescent : baseEnd_916636 < baseStart_916636 := by decide
  rcases family_descends (prefixWord ++ tailWord_916636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916640 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 4]
def baseStart_916640 : Nat := 118140960795 + 916640 * 2 ^ 59
def prefixEnd_916640 : Nat := 4983230072969 + 3 ^ 40 * 916640 * 2
def baseEnd_916640 : Nat := 418379473011021222652849

theorem tailTrace_916640 : CollatzResearch.WordTrace tailWord_916640 prefixEnd_916640 418379473011021222652849 := by
  unfold tailWord_916640
  simp only [CollatzResearch.WordTrace]
  refine ⟨16716303699588652246777687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22288404932784869662370249 16716303699588652246777687)
  ·
    refine ⟨25074455549382978370166531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16716303699588652246777687 25074455549382978370166531)
    ·
      refine ⟨37611683324074467555249797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25074455549382978370166531 37611683324074467555249797)
      ·
        refine ⟨7052190623263962666609337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37611683324074467555249797 7052190623263962666609337)
        ·
          refine ⟨5289142967447971999957003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7052190623263962666609337 5289142967447971999957003)
          ·
            refine ⟨7933714451171957999935505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5289142967447971999957003 7933714451171957999935505)
            ·
              refine ⟨5950285838378968499951629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7933714451171957999935505 5950285838378968499951629)
              ·
                refine ⟨2231357189392113187481861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5950285838378968499951629 2231357189392113187481861)
                ·
                  refine ⟨418379473011021222652849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2231357189392113187481861 418379473011021222652849)
                  ·
                    rfl

theorem cell20_916640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_916640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916640 prefixEnd_916640 := by exact prefixLift 916640
  have htrace : WordTrace (prefixWord ++ tailWord_916640) baseStart_916640 baseEnd_916640 := by
    simpa [prefixWord, tailWord_916640, baseEnd_916640] using wordTrace_append hprefix tailTrace_916640
  have hstable : (prefixWord ++ tailWord_916640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916640).length < 2 ^ (prefixWord ++ tailWord_916640).sum := by decide
  have hdescent : baseEnd_916640 < baseStart_916640 := by decide
  rcases family_descends (prefixWord ++ tailWord_916640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916657 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 4]
def baseStart_916657 : Nat := 118140960795 + 916657 * 2 ^ 59
def prefixEnd_916657 : Nat := 4983230072969 + 3 ^ 40 * 916657 * 2
def baseEnd_916657 : Nat := 418387232274244719086113

theorem tailTrace_916657 : CollatzResearch.WordTrace tailWord_916657 prefixEnd_916657 418387232274244719086113 := by
  unfold tailWord_916657
  simp only [CollatzResearch.WordTrace]
  refine ⟨33433227440115716396924225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22288818293410477597949483 33433227440115716396924225)
  ·
    refine ⟨25074920580086787297693169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33433227440115716396924225 25074920580086787297693169)
    ·
      refine ⟨18806190435065090473269877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25074920580086787297693169 18806190435065090473269877)
      ·
        refine ⟨1763080353287352231869051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18806190435065090473269877 1763080353287352231869051)
        ·
          refine ⟨2644620529931028347803577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1763080353287352231869051 2644620529931028347803577)
          ·
            refine ⟨1983465397448271260852683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2644620529931028347803577 1983465397448271260852683)
            ·
              refine ⟨2975198096172406891279025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983465397448271260852683 2975198096172406891279025)
              ·
                refine ⟨2231398572129305168459269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2975198096172406891279025 2231398572129305168459269)
                ·
                  refine ⟨418387232274244719086113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2231398572129305168459269 418387232274244719086113)
                  ·
                    rfl

theorem cell20_916657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_916657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916657 prefixEnd_916657 := by exact prefixLift 916657
  have htrace : WordTrace (prefixWord ++ tailWord_916657) baseStart_916657 baseEnd_916657 := by
    simpa [prefixWord, tailWord_916657, baseEnd_916657] using wordTrace_append hprefix tailTrace_916657
  have hstable : (prefixWord ++ tailWord_916657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916657).length < 2 ^ (prefixWord ++ tailWord_916657).sum := by decide
  have hdescent : baseEnd_916657 < baseStart_916657 := by decide
  rcases family_descends (prefixWord ++ tailWord_916657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916695 : List Nat := [1, 1, 3, 2, 1, 2, 4, 4, 2]
def baseStart_916695 : Nat := 118140960795 + 916695 * 2 ^ 59
def prefixEnd_916695 : Nat := 4983230072969 + 3 ^ 40 * 916695 * 2
def baseEnd_916695 : Nat := 418404576509685475819291

theorem tailTrace_916695 : CollatzResearch.WordTrace tailWord_916695 prefixEnd_916695 418404576509685475819291 := by
  unfold tailWord_916695
  simp only [CollatzResearch.WordTrace]
  refine ⟨33434613413978048886807539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22289742275985365924538359 33434613413978048886807539)
  ·
    refine ⟨50151920120967073330211309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33434613413978048886807539 50151920120967073330211309)
    ·
      refine ⟨18806970045362652498829241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50151920120967073330211309 18806970045362652498829241)
      ·
        refine ⟨14105227534021989374121931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18806970045362652498829241 14105227534021989374121931)
        ·
          refine ⟨21157841301032984061182897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14105227534021989374121931 21157841301032984061182897)
          ·
            refine ⟨15868380975774738045887173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21157841301032984061182897 15868380975774738045887173)
            ·
              refine ⟨2975321432957763383603845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15868380975774738045887173 2975321432957763383603845)
              ·
                refine ⟨557872768679580634425721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2975321432957763383603845 557872768679580634425721)
                ·
                  refine ⟨418404576509685475819291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557872768679580634425721 418404576509685475819291)
                  ·
                    rfl

theorem cell20_916695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 2].length) (baseStart_916695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916695 prefixEnd_916695 := by exact prefixLift 916695
  have htrace : WordTrace (prefixWord ++ tailWord_916695) baseStart_916695 baseEnd_916695 := by
    simpa [prefixWord, tailWord_916695, baseEnd_916695] using wordTrace_append hprefix tailTrace_916695
  have hstable : (prefixWord ++ tailWord_916695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916695).length < 2 ^ (prefixWord ++ tailWord_916695).sum := by decide
  have hdescent : baseEnd_916695 < baseStart_916695 := by decide
  rcases family_descends (prefixWord ++ tailWord_916695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916716 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 4]
def baseStart_916716 : Nat := 118140960795 + 916716 * 2 ^ 59
def prefixEnd_916716 : Nat := 4983230072969 + 3 ^ 40 * 916716 * 2
def baseEnd_916716 : Nat := 418414161481902736119205

theorem tailTrace_916716 : CollatzResearch.WordTrace tailWord_916716 prefixEnd_916716 418414161481902736119205 := by
  unfold tailWord_916716
  simp only [CollatzResearch.WordTrace]
  refine ⟨16717689673450984736661001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22290252897934646315548001 16717689673450984736661001)
  ·
    refine ⟨12538267255088238552495751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16717689673450984736661001 12538267255088238552495751)
    ·
      refine ⟨18807400882632357828743627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12538267255088238552495751 18807400882632357828743627)
      ·
        refine ⟨28211101323948536743115441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18807400882632357828743627 28211101323948536743115441)
        ·
          refine ⟨21158325992961402557336581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28211101323948536743115441 21158325992961402557336581)
          ·
            refine ⟨3967186123680262979500609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21158325992961402557336581 3967186123680262979500609)
            ·
              refine ⟨2975389592760197234625457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3967186123680262979500609 2975389592760197234625457)
              ·
                refine ⟨2231542194570147925969093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2975389592760197234625457 2231542194570147925969093)
                ·
                  refine ⟨418414161481902736119205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2231542194570147925969093 418414161481902736119205)
                  ·
                    rfl

theorem cell20_916716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_916716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916716 prefixEnd_916716 := by exact prefixLift 916716
  have htrace : WordTrace (prefixWord ++ tailWord_916716) baseStart_916716 baseEnd_916716 := by
    simpa [prefixWord, tailWord_916716, baseEnd_916716] using wordTrace_append hprefix tailTrace_916716
  have hstable : (prefixWord ++ tailWord_916716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916716).length < 2 ^ (prefixWord ++ tailWord_916716).sum := by decide
  have hdescent : baseEnd_916716 < baseStart_916716 := by decide
  rcases family_descends (prefixWord ++ tailWord_916716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916719 : List Nat := [1, 1, 2, 1, 7, 2, 2, 4]
def baseStart_916719 : Nat := 118140960795 + 916719 * 2 ^ 59
def prefixEnd_916719 : Nat := 4983230072969 + 3 ^ 40 * 916719 * 2
def baseEnd_916719 : Nat := 139471843587882686339731

theorem tailTrace_916719 : CollatzResearch.WordTrace tailWord_916719 prefixEnd_916719 139471843587882686339731 := by
  unfold tailWord_916719
  simp only [CollatzResearch.WordTrace]
  refine ⟨33435488765891100985681211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22290325843927400657120807 33435488765891100985681211)
  ·
    refine ⟨50153233148836651478521817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33435488765891100985681211 50153233148836651478521817)
    ·
      refine ⟨37614924861627488608891363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50153233148836651478521817 37614924861627488608891363)
      ·
        refine ⟨56422387292441232913337045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37614924861627488608891363 56422387292441232913337045)
        ·
          refine ⟨1322399702166591396406337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 56422387292441232913337045 1322399702166591396406337)
          ·
            refine ⟨991799776624943547304753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1322399702166591396406337 991799776624943547304753)
            ·
              refine ⟨743849832468707660478565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 991799776624943547304753 743849832468707660478565)
              ·
                refine ⟨139471843587882686339731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 743849832468707660478565 139471843587882686339731)
                ·
                  rfl

theorem cell20_916719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 4].length) (baseStart_916719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916719 prefixEnd_916719 := by exact prefixLift 916719
  have htrace : WordTrace (prefixWord ++ tailWord_916719) baseStart_916719 baseEnd_916719 := by
    simpa [prefixWord, tailWord_916719, baseEnd_916719] using wordTrace_append hprefix tailTrace_916719
  have hstable : (prefixWord ++ tailWord_916719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916719).length < 2 ^ (prefixWord ++ tailWord_916719).sum := by decide
  have hdescent : baseEnd_916719 < baseStart_916719 := by decide
  rcases family_descends (prefixWord ++ tailWord_916719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916723 : List Nat := [1, 1, 1, 2, 2, 6, 1, 6]
def baseStart_916723 : Nat := 118140960795 + 916723 * 2 ^ 59
def prefixEnd_916723 : Nat := 4983230072969 + 3 ^ 40 * 916723 * 2
def baseEnd_916723 : Nat := 139472452157547274295281

theorem tailTrace_916723 : CollatzResearch.WordTrace tailWord_916723 prefixEnd_916723 139472452157547274295281 := by
  unfold tailWord_916723
  simp only [CollatzResearch.WordTrace]
  refine ⟨33435634657876609668826823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22290423105251073112551215 33435634657876609668826823)
  ·
    refine ⟨50153451986814914503240235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33435634657876609668826823 50153451986814914503240235)
    ·
      refine ⟨75230177980222371754860353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50153451986814914503240235 75230177980222371754860353)
      ·
        refine ⟨56422633485166778816145265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75230177980222371754860353 56422633485166778816145265)
        ·
          refine ⟨42316975113875084112108949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56422633485166778816145265 42316975113875084112108949)
          ·
            refine ⟨1983608208462894567755107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42316975113875084112108949 1983608208462894567755107)
            ·
              refine ⟨2975412312694341851632661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983608208462894567755107 2975412312694341851632661)
              ·
                refine ⟨139472452157547274295281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2975412312694341851632661 139472452157547274295281)
                ·
                  rfl

theorem cell20_916723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 6].length) (baseStart_916723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916723 prefixEnd_916723 := by exact prefixLift 916723
  have htrace : WordTrace (prefixWord ++ tailWord_916723) baseStart_916723 baseEnd_916723 := by
    simpa [prefixWord, tailWord_916723, baseEnd_916723] using wordTrace_append hprefix tailTrace_916723
  have hstable : (prefixWord ++ tailWord_916723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916723).length < 2 ^ (prefixWord ++ tailWord_916723).sum := by decide
  have hdescent : baseEnd_916723 < baseStart_916723 := by decide
  rcases family_descends (prefixWord ++ tailWord_916723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916730 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_916730 : Nat := 118140960795 + 916730 * 2 ^ 59
def prefixEnd_916730 : Nat := 4983230072969 + 3 ^ 40 * 916730 * 2
def baseEnd_916730 : Nat := 418420551463380909652481

theorem tailTrace_916730 : CollatzResearch.WordTrace tailWord_916730 prefixEnd_916730 418420551463380909652481 := by
  unfold tailWord_916730
  simp only [CollatzResearch.WordTrace]
  refine ⟨8358972492212812466082911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22290593312567499909554429 8358972492212812466082911)
  ·
    refine ⟨12538458738319218699124367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8358972492212812466082911 12538458738319218699124367)
    ·
      refine ⟨18807688107478828048686551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12538458738319218699124367 18807688107478828048686551)
      ·
        refine ⟨28211532161218242073029827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18807688107478828048686551 28211532161218242073029827)
        ·
          refine ⟨42317298241827363109544741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28211532161218242073029827 42317298241827363109544741)
          ·
            refine ⟨7934493420342630583039639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42317298241827363109544741 7934493420342630583039639)
            ·
              refine ⟨11901740130513945874559459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7934493420342630583039639 11901740130513945874559459)
              ·
                refine ⟨17852610195770918811839189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11901740130513945874559459 17852610195770918811839189)
                ·
                  refine ⟨418420551463380909652481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17852610195770918811839189 418420551463380909652481)
                  ·
                    rfl

theorem cell20_916730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_916730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916730 prefixEnd_916730 := by exact prefixLift 916730
  have htrace : WordTrace (prefixWord ++ tailWord_916730) baseStart_916730 baseEnd_916730 := by
    simpa [prefixWord, tailWord_916730, baseEnd_916730] using wordTrace_append hprefix tailTrace_916730
  have hstable : (prefixWord ++ tailWord_916730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916730).length < 2 ^ (prefixWord ++ tailWord_916730).sum := by decide
  have hdescent : baseEnd_916730 < baseStart_916730 := by decide
  rcases family_descends (prefixWord ++ tailWord_916730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916740 : List Nat := [2, 3, 2, 2, 2, 3, 6]
def baseStart_916740 : Nat := 118140960795 + 916740 * 2 ^ 59
def prefixEnd_916740 : Nat := 4983230072969 + 3 ^ 40 * 916740 * 2
def baseEnd_916740 : Nat := 46491679526207257702123

theorem tailTrace_916740 : CollatzResearch.WordTrace tailWord_916740 prefixEnd_916740 46491679526207257702123 := by
  unfold tailWord_916740
  simp only [CollatzResearch.WordTrace]
  refine ⟨16718127349407510786097837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22290836465876681048130449 16718127349407510786097837)
  ·
    refine ⟨6269297756027816544786689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16718127349407510786097837 6269297756027816544786689)
    ·
      refine ⟨4701973317020862408590017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6269297756027816544786689 4701973317020862408590017)
      ·
        refine ⟨3526479987765646806442513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4701973317020862408590017 3526479987765646806442513)
        ·
          refine ⟨2644859990824235104831885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3526479987765646806442513 2644859990824235104831885)
          ·
            refine ⟨991822496559088164311957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2644859990824235104831885 991822496559088164311957)
            ·
              refine ⟨46491679526207257702123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 991822496559088164311957 46491679526207257702123)
              ·
                rfl

theorem cell20_916740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 6].length) (baseStart_916740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916740 prefixEnd_916740 := by exact prefixLift 916740
  have htrace : WordTrace (prefixWord ++ tailWord_916740) baseStart_916740 baseEnd_916740 := by
    simpa [prefixWord, tailWord_916740, baseEnd_916740] using wordTrace_append hprefix tailTrace_916740
  have hstable : (prefixWord ++ tailWord_916740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916740).length < 2 ^ (prefixWord ++ tailWord_916740).sum := by decide
  have hdescent : baseEnd_916740 < baseStart_916740 := by decide
  rcases family_descends (prefixWord ++ tailWord_916740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916764 : List Nat := [2, 2, 3, 1, 1, 1, 6, 1, 3]
def baseStart_916764 : Nat := 118140960795 + 916764 * 2 ^ 59
def prefixEnd_916764 : Nat := 4983230072969 + 3 ^ 40 * 916764 * 2
def baseEnd_916764 : Nat := 418436069989827902519009

theorem tailTrace_916764 : CollatzResearch.WordTrace tailWord_916764 prefixEnd_916764 418436069989827902519009 := by
  unfold tailWord_916764
  simp only [CollatzResearch.WordTrace]
  refine ⟨16718565025364036835534673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22291420033818715780712897 16718565025364036835534673)
  ·
    refine ⟨12538923769023027626651005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16718565025364036835534673 12538923769023027626651005)
    ·
      refine ⟨4702096413383635359994127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12538923769023027626651005 4702096413383635359994127)
      ·
        refine ⟨7053144620075453039991191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4702096413383635359994127 7053144620075453039991191)
        ·
          refine ⟨10579716930113179559986787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7053144620075453039991191 10579716930113179559986787)
          ·
            refine ⟨15869575395169769339980181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10579716930113179559986787 15869575395169769339980181)
            ·
              refine ⟨743886346648582937811571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15869575395169769339980181 743886346648582937811571)
              ·
                refine ⟨1115829519972874406717357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743886346648582937811571 1115829519972874406717357)
                ·
                  refine ⟨418436069989827902519009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1115829519972874406717357 418436069989827902519009)
                  ·
                    rfl

theorem cell20_916764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_916764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916764 prefixEnd_916764 := by exact prefixLift 916764
  have htrace : WordTrace (prefixWord ++ tailWord_916764) baseStart_916764 baseEnd_916764 := by
    simpa [prefixWord, tailWord_916764, baseEnd_916764] using wordTrace_append hprefix tailTrace_916764
  have hstable : (prefixWord ++ tailWord_916764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916764).length < 2 ^ (prefixWord ++ tailWord_916764).sum := by decide
  have hdescent : baseEnd_916764 < baseStart_916764 := by decide
  rcases family_descends (prefixWord ++ tailWord_916764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916778 : List Nat := [3, 1, 4, 2, 1, 1, 2, 6]
def baseStart_916778 : Nat := 118140960795 + 916778 * 2 ^ 59
def prefixEnd_916778 : Nat := 4983230072969 + 3 ^ 40 * 916778 * 2
def baseEnd_916778 : Nat := 139480819990435358684095

theorem tailTrace_916778 : CollatzResearch.WordTrace tailWord_916778 prefixEnd_916778 139480819990435358684095 := by
  unfold tailWord_916778
  simp only [CollatzResearch.WordTrace]
  refine ⟨8359410168169338515519747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22291760448451569374719325 8359410168169338515519747)
  ·
    refine ⟨12539115252254007773279621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8359410168169338515519747 12539115252254007773279621)
    ·
      refine ⟨2351084109797626457489929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12539115252254007773279621 2351084109797626457489929)
      ·
        refine ⟨1763313082348219843117447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2351084109797626457489929 1763313082348219843117447)
        ·
          refine ⟨2644969623522329764676171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1763313082348219843117447 2644969623522329764676171)
          ·
            refine ⟨3967454435283494647014257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644969623522329764676171 3967454435283494647014257)
            ·
              refine ⟨2975590826462620985260693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3967454435283494647014257 2975590826462620985260693)
              ·
                refine ⟨139480819990435358684095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2975590826462620985260693 139480819990435358684095)
                ·
                  rfl

theorem cell20_916778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_916778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916778 prefixEnd_916778 := by exact prefixLift 916778
  have htrace : WordTrace (prefixWord ++ tailWord_916778) baseStart_916778 baseEnd_916778 := by
    simpa [prefixWord, tailWord_916778, baseEnd_916778] using wordTrace_append hprefix tailTrace_916778
  have hstable : (prefixWord ++ tailWord_916778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916778).length < 2 ^ (prefixWord ++ tailWord_916778).sum := by decide
  have hdescent : baseEnd_916778 < baseStart_916778 := by decide
  rcases family_descends (prefixWord ++ tailWord_916778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916788 : List Nat := [2, 5, 1, 1, 1, 1, 2, 5, 2]
def baseStart_916788 : Nat := 118140960795 + 916788 * 2 ^ 59
def prefixEnd_916788 : Nat := 4983230072969 + 3 ^ 40 * 916788 * 2
def baseEnd_916788 : Nat := 418447024243790485718911

theorem tailTrace_916788 : CollatzResearch.WordTrace tailWord_916788 prefixEnd_916788 418447024243790485718911 := by
  unfold tailWord_916788
  simp only [CollatzResearch.WordTrace]
  refine ⟨16719002701320562884971509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22292003601760750513295345 16719002701320562884971509)
  ·
    refine ⟨1567406503248802770466079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16719002701320562884971509 1567406503248802770466079)
    ·
      refine ⟨2351109754873204155699119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1567406503248802770466079 2351109754873204155699119)
      ·
        refine ⟨3526664632309806233548679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2351109754873204155699119 3526664632309806233548679)
        ·
          refine ⟨5289996948464709350323019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3526664632309806233548679 5289996948464709350323019)
          ·
            refine ⟨7934995422697064025484529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5289996948464709350323019 7934995422697064025484529)
            ·
              refine ⟨5951246567022798019113397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7934995422697064025484529 5951246567022798019113397)
              ·
                refine ⟨557929365658387314291881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5951246567022798019113397 557929365658387314291881)
                ·
                  refine ⟨418447024243790485718911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557929365658387314291881 418447024243790485718911)
                  ·
                    rfl

theorem cell20_916788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_916788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916788 prefixEnd_916788 := by exact prefixLift 916788
  have htrace : WordTrace (prefixWord ++ tailWord_916788) baseStart_916788 baseEnd_916788 := by
    simpa [prefixWord, tailWord_916788, baseEnd_916788] using wordTrace_append hprefix tailTrace_916788
  have hstable : (prefixWord ++ tailWord_916788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916788).length < 2 ^ (prefixWord ++ tailWord_916788).sum := by decide
  have hdescent : baseEnd_916788 < baseStart_916788 := by decide
  rcases family_descends (prefixWord ++ tailWord_916788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916822 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_916822 : Nat := 118140960795 + 916822 * 2 ^ 59
def prefixEnd_916822 : Nat := 4983230072969 + 3 ^ 40 * 916822 * 2
def baseEnd_916822 : Nat := 418462542770237478585439

theorem tailTrace_916822 : CollatzResearch.WordTrace tailWord_916822 prefixEnd_916822 418462542770237478585439 := by
  unfold tailWord_916822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2089952842782371848542545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22292830323011966384453813 2089952842782371848542545)
  ·
    refine ⟨1567464632086778886406909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2089952842782371848542545 1567464632086778886406909)
    ·
      refine ⟨587799237032542082402591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1567464632086778886406909 587799237032542082402591)
      ·
        refine ⟨881698855548813123603887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587799237032542082402591 881698855548813123603887)
        ·
          refine ⟨1322548283323219685405831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881698855548813123603887 1322548283323219685405831)
          ·
            refine ⟨1983822424984829528108747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322548283323219685405831 1983822424984829528108747)
            ·
              refine ⟨2975733637477244292163121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983822424984829528108747 2975733637477244292163121)
              ·
                refine ⟨2231800228107933219122341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2975733637477244292163121 2231800228107933219122341)
                ·
                  refine ⟨418462542770237478585439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2231800228107933219122341 418462542770237478585439)
                  ·
                    rfl

theorem cell20_916822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_916822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916822 prefixEnd_916822 := by exact prefixLift 916822
  have htrace : WordTrace (prefixWord ++ tailWord_916822) baseStart_916822 baseEnd_916822 := by
    simpa [prefixWord, tailWord_916822, baseEnd_916822] using wordTrace_append hprefix tailTrace_916822
  have hstable : (prefixWord ++ tailWord_916822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916822).length < 2 ^ (prefixWord ++ tailWord_916822).sum := by decide
  have hdescent : baseEnd_916822 < baseStart_916822 := by decide
  rcases family_descends (prefixWord ++ tailWord_916822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916823 : List Nat := [1, 1, 3, 2, 3, 2, 2, 3, 3]
def baseStart_916823 : Nat := 118140960795 + 916823 * 2 ^ 59
def prefixEnd_916823 : Nat := 4983230072969 + 3 ^ 40 * 916823 * 2
def baseEnd_916823 : Nat := 418462999197485919552101

theorem tailTrace_916823 : CollatzResearch.WordTrace tailWord_916823 prefixEnd_916823 418462999197485919552101 := by
  unfold tailWord_916823
  simp only [CollatzResearch.WordTrace]
  refine ⟨33439281957514326747467123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22292854638342884498311415 33439281957514326747467123)
  ·
    refine ⟨50158922936271490121200685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33439281957514326747467123 50158922936271490121200685)
    ·
      refine ⟨18809596101101808795450257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50158922936271490121200685 18809596101101808795450257)
      ·
        refine ⟨14107197075826356596587693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18809596101101808795450257 14107197075826356596587693)
        ·
          refine ⟨5290198903434883723720385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14107197075826356596587693 5290198903434883723720385)
          ·
            refine ⟨3967649177576162792790289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5290198903434883723720385 3967649177576162792790289)
            ·
              refine ⟨2975736883182122094592717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3967649177576162792790289 2975736883182122094592717)
              ·
                refine ⟨1115901331193295785472269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2975736883182122094592717 1115901331193295785472269)
                ·
                  refine ⟨418462999197485919552101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1115901331193295785472269 418462999197485919552101)
                  ·
                    rfl

theorem cell20_916823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 3].length) (baseStart_916823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916823 prefixEnd_916823 := by exact prefixLift 916823
  have htrace : WordTrace (prefixWord ++ tailWord_916823) baseStart_916823 baseEnd_916823 := by
    simpa [prefixWord, tailWord_916823, baseEnd_916823] using wordTrace_append hprefix tailTrace_916823
  have hstable : (prefixWord ++ tailWord_916823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916823).length < 2 ^ (prefixWord ++ tailWord_916823).sum := by decide
  have hdescent : baseEnd_916823 < baseStart_916823 := by decide
  rcases family_descends (prefixWord ++ tailWord_916823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916829 : List Nat := [1, 4, 5, 1, 1, 1, 3, 4]
def baseStart_916829 : Nat := 118140960795 + 916829 * 2 ^ 59
def prefixEnd_916829 : Nat := 4983230072969 + 3 ^ 40 * 916829 * 2
def baseEnd_916829 : Nat := 139488579253658855117359

theorem tailTrace_916829 : CollatzResearch.WordTrace tailWord_916829 prefixEnd_916829 139488579253658855117359 := by
  unfold tailWord_916829
  simp only [CollatzResearch.WordTrace]
  refine ⟨33439500795492589772185541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22293000530328393181457027 33439500795492589772185541)
  ·
    refine ⟨6269906399154860582284789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33439500795492589772185541 6269906399154860582284789)
    ·
      refine ⟨587803724920768179589199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6269906399154860582284789 587803724920768179589199)
      ·
        refine ⟨881705587381152269383799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587803724920768179589199 881705587381152269383799)
        ·
          refine ⟨1322558381071728404075699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881705587381152269383799 1322558381071728404075699)
          ·
            refine ⟨1983837571607592606113549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322558381071728404075699 1983837571607592606113549)
            ·
              refine ⟨743939089352847227292581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1983837571607592606113549 743939089352847227292581)
              ·
                refine ⟨139488579253658855117359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 743939089352847227292581 139488579253658855117359)
                ·
                  rfl

theorem cell20_916829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 4].length) (baseStart_916829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916829 prefixEnd_916829 := by exact prefixLift 916829
  have htrace : WordTrace (prefixWord ++ tailWord_916829) baseStart_916829 baseEnd_916829 := by
    simpa [prefixWord, tailWord_916829, baseEnd_916829] using wordTrace_append hprefix tailTrace_916829
  have hstable : (prefixWord ++ tailWord_916829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916829).length < 2 ^ (prefixWord ++ tailWord_916829).sum := by decide
  have hdescent : baseEnd_916829 < baseStart_916829 := by decide
  rcases family_descends (prefixWord ++ tailWord_916829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916847 : List Nat := [1, 1, 2, 1, 3, 1, 6, 3, 2]
def baseStart_916847 : Nat := 118140960795 + 916847 * 2 ^ 59
def prefixEnd_916847 : Nat := 4983230072969 + 3 ^ 40 * 916847 * 2
def baseEnd_916847 : Nat := 418473953451448502752003

theorem tailTrace_916847 : CollatzResearch.WordTrace tailWord_916847 prefixEnd_916847 418473953451448502752003 := by
  unfold tailWord_916847
  simp only [CollatzResearch.WordTrace]
  refine ⟨33440157309427378846340795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22293438206284919230893863 33440157309427378846340795)
  ·
    refine ⟨50160235964141068269511193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33440157309427378846340795 50160235964141068269511193)
    ·
      refine ⟨37620176973105801202133395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50160235964141068269511193 37620176973105801202133395)
      ·
        refine ⟨56430265459658701803200093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37620176973105801202133395 56430265459658701803200093)
        ·
          refine ⟨21161349547372013176200035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56430265459658701803200093 21161349547372013176200035)
          ·
            refine ⟨31742024321058019764300053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21161349547372013176200035 31742024321058019764300053)
            ·
              refine ⟨1487907390049594676451565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31742024321058019764300053 1487907390049594676451565)
              ·
                refine ⟨557965271268598003669337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1487907390049594676451565 557965271268598003669337)
                ·
                  refine ⟨418473953451448502752003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557965271268598003669337 418473953451448502752003)
                  ·
                    rfl

theorem cell20_916847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 2].length) (baseStart_916847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916847 prefixEnd_916847 := by exact prefixLift 916847
  have htrace : WordTrace (prefixWord ++ tailWord_916847) baseStart_916847 baseEnd_916847 := by
    simpa [prefixWord, tailWord_916847, baseEnd_916847] using wordTrace_append hprefix tailTrace_916847
  have hstable : (prefixWord ++ tailWord_916847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916847).length < 2 ^ (prefixWord ++ tailWord_916847).sum := by decide
  have hdescent : baseEnd_916847 < baseStart_916847 := by decide
  rcases family_descends (prefixWord ++ tailWord_916847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916868 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 4]
def baseStart_916868 : Nat := 118140960795 + 916868 * 2 ^ 59
def prefixEnd_916868 : Nat := 4983230072969 + 3 ^ 40 * 916868 * 2
def baseEnd_916868 : Nat := 418483538423665763051917

theorem tailTrace_916868 : CollatzResearch.WordTrace tailWord_916868 prefixEnd_916868 418483538423665763051917 := by
  unfold tailWord_916868
  simp only [CollatzResearch.WordTrace]
  refine ⟨16720461621175649716427629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22293948828234199621903505 16720461621175649716427629)
  ·
    refine ⟨6270173107940868643660361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16720461621175649716427629 6270173107940868643660361)
    ·
      refine ⟨4702629830955651482745271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6270173107940868643660361 4702629830955651482745271)
      ·
        refine ⟨7053944746433477224117907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4702629830955651482745271 7053944746433477224117907)
        ·
          refine ⟨10580917119650215836176861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7053944746433477224117907 10580917119650215836176861)
          ·
            refine ⟨3967843919868830938566323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10580917119650215836176861 3967843919868830938566323)
            ·
              refine ⟨5951765879803246407849485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3967843919868830938566323 5951765879803246407849485)
              ·
                refine ⟨2231912204926217402943557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5951765879803246407849485 2231912204926217402943557)
                ·
                  refine ⟨418483538423665763051917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2231912204926217402943557 418483538423665763051917)
                  ·
                    rfl

theorem cell20_916868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_916868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916868 prefixEnd_916868 := by exact prefixLift 916868
  have htrace : WordTrace (prefixWord ++ tailWord_916868) baseStart_916868 baseEnd_916868 := by
    simpa [prefixWord, tailWord_916868, baseEnd_916868] using wordTrace_append hprefix tailTrace_916868
  have hstable : (prefixWord ++ tailWord_916868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916868).length < 2 ^ (prefixWord ++ tailWord_916868).sum := by decide
  have hdescent : baseEnd_916868 < baseStart_916868 := by decide
  rcases family_descends (prefixWord ++ tailWord_916868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916888 : List Nat := [2, 1, 2, 5, 3, 1, 2, 4]
def baseStart_916888 : Nat := 118140960795 + 916888 * 2 ^ 59
def prefixEnd_916888 : Nat := 4983230072969 + 3 ^ 40 * 916888 * 2
def baseEnd_916888 : Nat := 139497555656211527461723

theorem tailTrace_916888 : CollatzResearch.WordTrace tailWord_916888 prefixEnd_916888 139497555656211527461723 := by
  unfold tailWord_916888
  simp only [CollatzResearch.WordTrace]
  refine ⟨16720826351139421424291659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22294435134852561899055545 16720826351139421424291659)
  ·
    refine ⟨25081239526709132136437489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16720826351139421424291659 25081239526709132136437489)
    ·
      refine ⟨18810929645031849102328117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25081239526709132136437489 18810929645031849102328117)
      ·
        refine ⟨1763524654221735853343261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18810929645031849102328117 1763524654221735853343261)
        ·
          refine ⟨661321745333150945003723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1763524654221735853343261 661321745333150945003723)
          ·
            refine ⟨991982617999726417505585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661321745333150945003723 991982617999726417505585)
            ·
              refine ⟨743986963499794813129189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 991982617999726417505585 743986963499794813129189)
              ·
                refine ⟨139497555656211527461723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 743986963499794813129189 139497555656211527461723)
                ·
                  rfl

theorem cell20_916888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 4].length) (baseStart_916888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916888 prefixEnd_916888 := by exact prefixLift 916888
  have htrace : WordTrace (prefixWord ++ tailWord_916888) baseStart_916888 baseEnd_916888 := by
    simpa [prefixWord, tailWord_916888, baseEnd_916888] using wordTrace_append hprefix tailTrace_916888
  have hstable : (prefixWord ++ tailWord_916888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916888).length < 2 ^ (prefixWord ++ tailWord_916888).sum := by decide
  have hdescent : baseEnd_916888 < baseStart_916888 := by decide
  rcases family_descends (prefixWord ++ tailWord_916888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916920 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 5]
def baseStart_916920 : Nat := 118140960795 + 916920 * 2 ^ 59
def prefixEnd_916920 : Nat := 4983230072969 + 3 ^ 40 * 916920 * 2
def baseEnd_916920 : Nat := 418507272640584693318371

theorem tailTrace_916920 : CollatzResearch.WordTrace tailWord_916920 prefixEnd_916920 418507272640584693318371 := by
  unfold tailWord_916920
  simp only [CollatzResearch.WordTrace]
  refine ⟨16721409919081456156874107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22295213225441941542498809 16721409919081456156874107)
  ·
    refine ⟨25082114878622184235311161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16721409919081456156874107 25082114878622184235311161)
    ·
      refine ⟨18811586158966638176483371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25082114878622184235311161 18811586158966638176483371)
      ·
        refine ⟨28217379238449957264725057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18811586158966638176483371 28217379238449957264725057)
        ·
          refine ⟨21163034428837467948543793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28217379238449957264725057 21163034428837467948543793)
          ·
            refine ⟨15872275821628100961407845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21163034428837467948543793 15872275821628100961407845)
            ·
              refine ⟨2976051716555268930263971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15872275821628100961407845 2976051716555268930263971)
              ·
                refine ⟨4464077574832903395395957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2976051716555268930263971 4464077574832903395395957)
                ·
                  refine ⟨418507272640584693318371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4464077574832903395395957 418507272640584693318371)
                  ·
                    rfl

theorem cell20_916920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_916920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916920 prefixEnd_916920 := by exact prefixLift 916920
  have htrace : WordTrace (prefixWord ++ tailWord_916920) baseStart_916920 baseEnd_916920 := by
    simpa [prefixWord, tailWord_916920, baseEnd_916920] using wordTrace_append hprefix tailTrace_916920
  have hstable : (prefixWord ++ tailWord_916920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916920).length < 2 ^ (prefixWord ++ tailWord_916920).sum := by decide
  have hdescent : baseEnd_916920 < baseStart_916920 := by decide
  rcases family_descends (prefixWord ++ tailWord_916920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916978 : List Nat := [3, 2, 1, 4, 1, 2, 1, 4, 2]
def baseStart_916978 : Nat := 118140960795 + 916978 * 2 ^ 59
def prefixEnd_916978 : Nat := 4983230072969 + 3 ^ 40 * 916978 * 2
def baseEnd_916978 : Nat := 418533745420994269384801

theorem tailTrace_916978 : CollatzResearch.WordTrace tailWord_916978 prefixEnd_916978 418533745420994269384801 := by
  unfold tailWord_916978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8361233817988197054839897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22296623514635192146239725 8361233817988197054839897)
  ·
    refine ⟨6270925363491147791129923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8361233817988197054839897 6270925363491147791129923)
    ·
      refine ⟨9406388045236721686694885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6270925363491147791129923 9406388045236721686694885)
      ·
        refine ⟨1763697758481885316255291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9406388045236721686694885 1763697758481885316255291)
        ·
          refine ⟨2645546637722827974382937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1763697758481885316255291 2645546637722827974382937)
          ·
            refine ⟨1984159978292120980787203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2645546637722827974382937 1984159978292120980787203)
            ·
              refine ⟨2976239967438181471180805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1984159978292120980787203 2976239967438181471180805)
              ·
                refine ⟨558044993894659025846401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2976239967438181471180805 558044993894659025846401)
                ·
                  refine ⟨418533745420994269384801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558044993894659025846401 418533745420994269384801)
                  ·
                    rfl

theorem cell20_916978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_916978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916978 prefixEnd_916978 := by exact prefixLift 916978
  have htrace : WordTrace (prefixWord ++ tailWord_916978) baseStart_916978 baseEnd_916978 := by
    simpa [prefixWord, tailWord_916978, baseEnd_916978] using wordTrace_append hprefix tailTrace_916978
  have hstable : (prefixWord ++ tailWord_916978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916978).length < 2 ^ (prefixWord ++ tailWord_916978).sum := by decide
  have hdescent : baseEnd_916978 < baseStart_916978 := by decide
  rcases family_descends (prefixWord ++ tailWord_916978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916989 : List Nat := [1, 4, 1, 1, 1, 4, 3, 5]
def baseStart_916989 : Nat := 118140960795 + 916989 * 2 ^ 59
def prefixEnd_916989 : Nat := 4983230072969 + 3 ^ 40 * 916989 * 2
def baseEnd_916989 : Nat := 139512922040242373339363

theorem tailTrace_916989 : CollatzResearch.WordTrace tailWord_916989 prefixEnd_916989 139512922040242373339363 := by
  unfold tailWord_916989
  simp only [CollatzResearch.WordTrace]
  refine ⟨33445336474912937098010021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22296890983275291398673347 33445336474912937098010021)
  ·
    refine ⟨6271000589046175705876879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33445336474912937098010021 6271000589046175705876879)
    ·
      refine ⟨9406500883569263558815319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6271000589046175705876879 9406500883569263558815319)
      ·
        refine ⟨14109751325353895338222979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9406500883569263558815319 14109751325353895338222979)
        ·
          refine ⟨21164626988030843007334469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14109751325353895338222979 21164626988030843007334469)
          ·
            refine ⟨3968367560255783063875213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21164626988030843007334469 3968367560255783063875213)
            ·
              refine ⟨1488137835095918648953205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3968367560255783063875213 1488137835095918648953205)
              ·
                refine ⟨139512922040242373339363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1488137835095918648953205 139512922040242373339363)
                ·
                  rfl

theorem cell20_916989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 5].length) (baseStart_916989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_916989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_916989 prefixEnd_916989 := by exact prefixLift 916989
  have htrace : WordTrace (prefixWord ++ tailWord_916989) baseStart_916989 baseEnd_916989 := by
    simpa [prefixWord, tailWord_916989, baseEnd_916989] using wordTrace_append hprefix tailTrace_916989
  have hstable : (prefixWord ++ tailWord_916989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916989).length < 2 ^ (prefixWord ++ tailWord_916989).sum := by decide
  have hdescent : baseEnd_916989 < baseStart_916989 := by decide
  rcases family_descends (prefixWord ++ tailWord_916989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917016 : List Nat := [2, 1, 2, 3, 4, 1, 2, 3, 2]
def baseStart_917016 : Nat := 118140960795 + 917016 * 2 ^ 59
def prefixEnd_917016 : Nat := 4983230072969 + 3 ^ 40 * 917016 * 2
def baseEnd_917016 : Nat := 418551089656435026117979

theorem tailTrace_917016 : CollatzResearch.WordTrace tailWord_917016 prefixEnd_917016 418551089656435026117979 := by
  unfold tailWord_917016
  simp only [CollatzResearch.WordTrace]
  refine ⟨16723160622907560354621451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22297547497210080472828601 16723160622907560354621451)
  ·
    refine ⟨25084740934361340531932177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16723160622907560354621451 25084740934361340531932177)
    ·
      refine ⟨18813555700771005398949133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25084740934361340531932177 18813555700771005398949133)
      ·
        refine ⟨7055083387789127024605925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18813555700771005398949133 7055083387789127024605925)
        ·
          refine ⟨1322828135210461317113611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7055083387789127024605925 1322828135210461317113611)
          ·
            refine ⟨1984242202815691975670417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322828135210461317113611 1984242202815691975670417)
            ·
              refine ⟨1488181652111768981752813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1984242202815691975670417 1488181652111768981752813)
              ·
                refine ⟨558068119541913368157305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1488181652111768981752813 558068119541913368157305)
                ·
                  refine ⟨418551089656435026117979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558068119541913368157305 418551089656435026117979)
                  ·
                    rfl

theorem cell20_917016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 2].length) (baseStart_917016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917016 prefixEnd_917016 := by exact prefixLift 917016
  have htrace : WordTrace (prefixWord ++ tailWord_917016) baseStart_917016 baseEnd_917016 := by
    simpa [prefixWord, tailWord_917016, baseEnd_917016] using wordTrace_append hprefix tailTrace_917016
  have hstable : (prefixWord ++ tailWord_917016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917016).length < 2 ^ (prefixWord ++ tailWord_917016).sum := by decide
  have hdescent : baseEnd_917016 < baseStart_917016 := by decide
  rcases family_descends (prefixWord ++ tailWord_917016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917022 : List Nat := [4, 3, 3, 1, 2, 1, 1, 2, 3]
def baseStart_917022 : Nat := 118140960795 + 917022 * 2 ^ 59
def prefixEnd_917022 : Nat := 4983230072969 + 3 ^ 40 * 917022 * 2
def baseEnd_917022 : Nat := 418553828219925671917955

theorem tailTrace_917022 : CollatzResearch.WordTrace tailWord_917022 prefixEnd_917022 418553828219925671917955 := by
  unfold tailWord_917022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4180817510474172966745165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22297693389195589155974213 4180817510474172966745165)
  ·
    refine ⟨1567806566427814862529437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4180817510474172966745165 1567806566427814862529437)
    ·
      refine ⟨587927462410430573448539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1567806566427814862529437 587927462410430573448539)
      ·
        refine ⟨881891193615645860172809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587927462410430573448539 881891193615645860172809)
        ·
          refine ⟨661418395211734395129607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 881891193615645860172809 661418395211734395129607)
          ·
            refine ⟨992127592817601592694411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661418395211734395129607 992127592817601592694411)
            ·
              refine ⟨1488191389226402389041617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992127592817601592694411 1488191389226402389041617)
              ·
                refine ⟨1116143541919801791781213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1488191389226402389041617 1116143541919801791781213)
                ·
                  refine ⟨418553828219925671917955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1116143541919801791781213 418553828219925671917955)
                  ·
                    rfl

theorem cell20_917022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_917022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917022 prefixEnd_917022 := by exact prefixLift 917022
  have htrace : WordTrace (prefixWord ++ tailWord_917022) baseStart_917022 baseEnd_917022 := by
    simpa [prefixWord, tailWord_917022, baseEnd_917022] using wordTrace_append hprefix tailTrace_917022
  have hstable : (prefixWord ++ tailWord_917022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917022).length < 2 ^ (prefixWord ++ tailWord_917022).sum := by decide
  have hdescent : baseEnd_917022 < baseStart_917022 := by decide
  rcases family_descends (prefixWord ++ tailWord_917022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917027 : List Nat := [1, 1, 1, 4, 5, 1, 7]
def baseStart_917027 : Nat := 118140960795 + 917027 * 2 ^ 59
def prefixEnd_917027 : Nat := 4983230072969 + 3 ^ 40 * 917027 * 2
def baseEnd_917027 : Nat := 46506234484018652972363

theorem tailTrace_917027 : CollatzResearch.WordTrace tailWord_917027 prefixEnd_917027 46506234484018652972363 := by
  unfold tailWord_917027
  simp only [CollatzResearch.WordTrace]
  refine ⟨33446722448775269587893335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22297814965850179725262223 33446722448775269587893335)
  ·
    refine ⟨50170083673162904381840003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33446722448775269587893335 50170083673162904381840003)
    ·
      refine ⟨75255125509744356572760005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50170083673162904381840003 75255125509744356572760005)
      ·
        refine ⟨14110336033077066857392501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75255125509744356572760005 14110336033077066857392501)
        ·
          refine ⟨1322844003100975017880547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14110336033077066857392501 1322844003100975017880547)
          ·
            refine ⟨1984266004651462526820821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322844003100975017880547 1984266004651462526820821)
            ·
              refine ⟨46506234484018652972363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1984266004651462526820821 46506234484018652972363)
              ·
                rfl

theorem cell20_917027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 7].length) (baseStart_917027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917027 prefixEnd_917027 := by exact prefixLift 917027
  have htrace : WordTrace (prefixWord ++ tailWord_917027) baseStart_917027 baseEnd_917027 := by
    simpa [prefixWord, tailWord_917027, baseEnd_917027] using wordTrace_append hprefix tailTrace_917027
  have hstable : (prefixWord ++ tailWord_917027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917027).length < 2 ^ (prefixWord ++ tailWord_917027).sum := by decide
  have hdescent : baseEnd_917027 < baseStart_917027 := by decide
  rcases family_descends (prefixWord ++ tailWord_917027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917078 : List Nat := [5, 2, 2, 2, 1, 2, 6]
def baseStart_917078 : Nat := 118140960795 + 917078 * 2 ^ 59
def prefixEnd_917078 : Nat := 4983230072969 + 3 ^ 40 * 917078 * 2
def baseEnd_917078 : Nat := 46508820905093151783451

theorem tailTrace_917078 : CollatzResearch.WordTrace tailWord_917078 prefixEnd_917078 46508820905093151783451 := by
  unfold tailWord_917078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2090536410724406581124993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22299055047727003531999925 2090536410724406581124993)
  ·
    refine ⟨1567902308043304935843745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2090536410724406581124993 1567902308043304935843745)
    ·
      refine ⟨1175926731032478701882809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1567902308043304935843745 1175926731032478701882809)
      ·
        refine ⟨881945048274359026412107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1175926731032478701882809 881945048274359026412107)
        ·
          refine ⟨1322917572411538539618161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881945048274359026412107 1322917572411538539618161)
          ·
            refine ⟨992188179308653904713621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1322917572411538539618161 992188179308653904713621)
            ·
              refine ⟨46508820905093151783451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 992188179308653904713621 46508820905093151783451)
              ·
                rfl

theorem cell20_917078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 6].length) (baseStart_917078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917078 prefixEnd_917078 := by exact prefixLift 917078
  have htrace : WordTrace (prefixWord ++ tailWord_917078) baseStart_917078 baseEnd_917078 := by
    simpa [prefixWord, tailWord_917078, baseEnd_917078] using wordTrace_append hprefix tailTrace_917078
  have hstable : (prefixWord ++ tailWord_917078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917078).length < 2 ^ (prefixWord ++ tailWord_917078).sum := by decide
  have hdescent : baseEnd_917078 < baseStart_917078 := by decide
  rcases family_descends (prefixWord ++ tailWord_917078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917092 : List Nat := [2, 3, 1, 1, 2, 4, 3, 2, 2]
def baseStart_917092 : Nat := 118140960795 + 917092 * 2 ^ 59
def prefixEnd_917092 : Nat := 4983230072969 + 3 ^ 40 * 917092 * 2
def baseEnd_917092 : Nat := 418585778127316539584335

theorem tailTrace_917092 : CollatzResearch.WordTrace tailWord_917092 prefixEnd_917092 418585778127316539584335 := by
  unfold tailWord_917092
  simp only [CollatzResearch.WordTrace]
  refine ⟨16724546596769892844504765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22299395462359857126006353 16724546596769892844504765)
  ·
    refine ⟨6271704973788709816689287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16724546596769892844504765 6271704973788709816689287)
    ·
      refine ⟨9407557460683064725033931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6271704973788709816689287 9407557460683064725033931)
      ·
        refine ⟨14111336191024597087550897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9407557460683064725033931 14111336191024597087550897)
        ·
          refine ⟨10583502143268447815663173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14111336191024597087550897 10583502143268447815663173)
          ·
            refine ⟨1984406651862833965436845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10583502143268447815663173 1984406651862833965436845)
            ·
              refine ⟨744152494448562737038817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1984406651862833965436845 744152494448562737038817)
              ·
                refine ⟨558114370836422052779113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 744152494448562737038817 558114370836422052779113)
                ·
                  refine ⟨418585778127316539584335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558114370836422052779113 418585778127316539584335)
                  ·
                    rfl

theorem cell20_917092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_917092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917092 prefixEnd_917092 := by exact prefixLift 917092
  have htrace : WordTrace (prefixWord ++ tailWord_917092) baseStart_917092 baseEnd_917092 := by
    simpa [prefixWord, tailWord_917092, baseEnd_917092] using wordTrace_append hprefix tailTrace_917092
  have hstable : (prefixWord ++ tailWord_917092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917092).length < 2 ^ (prefixWord ++ tailWord_917092).sum := by decide
  have hdescent : baseEnd_917092 < baseStart_917092 := by decide
  rcases family_descends (prefixWord ++ tailWord_917092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917102 : List Nat := [4, 1, 2, 2, 4, 1, 2, 1, 3]
def baseStart_917102 : Nat := 118140960795 + 917102 * 2 ^ 59
def prefixEnd_917102 : Nat := 4983230072969 + 3 ^ 40 * 917102 * 2
def baseEnd_917102 : Nat := 418590342399800949250961

theorem tailTrace_917102 : CollatzResearch.WordTrace tailWord_917102 prefixEnd_917102 418590342399800949250961 := by
  unfold tailWord_917102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4181182240437944674609195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22299638615669038264582373 4181182240437944674609195)
  ·
    refine ⟨6271773360656917011913793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4181182240437944674609195 6271773360656917011913793)
    ·
      refine ⟨4703830020492687758935345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6271773360656917011913793 4703830020492687758935345)
      ·
        refine ⟨3527872515369515819201509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4703830020492687758935345 3527872515369515819201509)
        ·
          refine ⟨661476096631784216100283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3527872515369515819201509 661476096631784216100283)
          ·
            refine ⟨992214144947676324150425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661476096631784216100283 992214144947676324150425)
            ·
              refine ⟨744160608710757243112819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992214144947676324150425 744160608710757243112819)
              ·
                refine ⟨1116240913066135864669229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744160608710757243112819 1116240913066135864669229)
                ·
                  refine ⟨418590342399800949250961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1116240913066135864669229 418590342399800949250961)
                  ·
                    rfl

theorem cell20_917102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_917102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917102 prefixEnd_917102 := by exact prefixLift 917102
  have htrace : WordTrace (prefixWord ++ tailWord_917102) baseStart_917102 baseEnd_917102 := by
    simpa [prefixWord, tailWord_917102, baseEnd_917102] using wordTrace_append hprefix tailTrace_917102
  have hstable : (prefixWord ++ tailWord_917102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917102).length < 2 ^ (prefixWord ++ tailWord_917102).sum := by decide
  have hdescent : baseEnd_917102 < baseStart_917102 := by decide
  rcases family_descends (prefixWord ++ tailWord_917102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917106 : List Nat := [3, 2, 1, 2, 3, 1, 4, 1, 3]
def baseStart_917106 : Nat := 118140960795 + 917106 * 2 ^ 59
def prefixEnd_917106 : Nat := 4983230072969 + 3 ^ 40 * 917106 * 2
def baseEnd_917106 : Nat := 418592168108794713117611

theorem tailTrace_917106 : CollatzResearch.WordTrace tailWord_917106 prefixEnd_917106 418592168108794713117611 := by
  unfold tailWord_917106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8362400953872266520004793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22299735876992710720012781 8362400953872266520004793)
  ·
    refine ⟨6271800715404199890003595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8362400953872266520004793 6271800715404199890003595)
    ·
      refine ⟨9407701073106299835005393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6271800715404199890003595 9407701073106299835005393)
      ·
        refine ⟨7055775804829724876254045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9407701073106299835005393 7055775804829724876254045)
        ·
          refine ⟨2645915926811146828595267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7055775804829724876254045 2645915926811146828595267)
          ·
            refine ⟨3968873890216720242892901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2645915926811146828595267 3968873890216720242892901)
            ·
              refine ⟨744163854415635045542419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3968873890216720242892901 744163854415635045542419)
              ·
                refine ⟨1116245781623452568313629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744163854415635045542419 1116245781623452568313629)
                ·
                  refine ⟨418592168108794713117611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1116245781623452568313629 418592168108794713117611)
                  ·
                    rfl

theorem cell20_917106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_917106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917106 prefixEnd_917106 := by exact prefixLift 917106
  have htrace : WordTrace (prefixWord ++ tailWord_917106) baseStart_917106 baseEnd_917106 := by
    simpa [prefixWord, tailWord_917106, baseEnd_917106] using wordTrace_append hprefix tailTrace_917106
  have hstable : (prefixWord ++ tailWord_917106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917106).length < 2 ^ (prefixWord ++ tailWord_917106).sum := by decide
  have hdescent : baseEnd_917106 < baseStart_917106 := by decide
  rcases family_descends (prefixWord ++ tailWord_917106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917154 : List Nat := [3, 3, 1, 4, 2, 1, 1, 5]
def baseStart_917154 : Nat := 118140960795 + 917154 * 2 ^ 59
def prefixEnd_917154 : Nat := 4983230072969 + 3 ^ 40 * 917154 * 2
def baseEnd_917154 : Nat := 139538025538906626505805

theorem tailTrace_917154 : CollatzResearch.WordTrace tailWord_917154 prefixEnd_917154 139538025538906626505805 := by
  unfold tailWord_917154
  simp only [CollatzResearch.WordTrace]
  refine ⟨8362838629828792569441629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22300903012876780185177677 8362838629828792569441629)
  ·
    refine ⟨3136064486185797213540611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8362838629828792569441629 3136064486185797213540611)
    ·
      refine ⟨4704096729278695820310917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3136064486185797213540611 4704096729278695820310917)
      ·
        refine ⟨882018136739755466308297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4704096729278695820310917 882018136739755466308297)
        ·
          refine ⟨661513602554816599731223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 882018136739755466308297 661513602554816599731223)
          ·
            refine ⟨992270403832224899596835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661513602554816599731223 992270403832224899596835)
            ·
              refine ⟨1488405605748337349395253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992270403832224899596835 1488405605748337349395253)
              ·
                refine ⟨139538025538906626505805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1488405605748337349395253 139538025538906626505805)
                ·
                  rfl

theorem cell20_917154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_917154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917154 prefixEnd_917154 := by exact prefixLift 917154
  have htrace : WordTrace (prefixWord ++ tailWord_917154) baseStart_917154 baseEnd_917154 := by
    simpa [prefixWord, tailWord_917154, baseEnd_917154] using wordTrace_append hprefix tailTrace_917154
  have hstable : (prefixWord ++ tailWord_917154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917154).length < 2 ^ (prefixWord ++ tailWord_917154).sum := by decide
  have hdescent : baseEnd_917154 < baseStart_917154 := by decide
  rcases family_descends (prefixWord ++ tailWord_917154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917155 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 4]
def baseStart_917155 : Nat := 118140960795 + 917155 * 2 ^ 59
def prefixEnd_917155 : Nat := 4983230072969 + 3 ^ 40 * 917155 * 2
def baseEnd_917155 : Nat := 418614533043968320484077

theorem tailTrace_917155 : CollatzResearch.WordTrace tailWord_917155 prefixEnd_917155 418614533043968320484077 := by
  unfold tailWord_917155
  simp only [CollatzResearch.WordTrace]
  refine ⟨33451390992311547448552919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22300927328207698299035279 33451390992311547448552919)
  ·
    refine ⟨50177086488467321172829379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33451390992311547448552919 50177086488467321172829379)
    ·
      refine ⟨75265629732700981759244069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50177086488467321172829379 75265629732700981759244069)
      ·
        refine ⟨14112305574881434079858263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75265629732700981759244069 14112305574881434079858263)
        ·
          refine ⟨21168458362322151119787395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14112305574881434079858263 21168458362322151119787395)
          ·
            refine ⟨31752687543483226679681093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21168458362322151119787395 31752687543483226679681093)
            ·
              refine ⟨5953628914403105002440205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31752687543483226679681093 5953628914403105002440205)
              ·
                refine ⟨2232610842901164375915077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5953628914403105002440205 2232610842901164375915077)
                ·
                  refine ⟨418614533043968320484077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2232610842901164375915077 418614533043968320484077)
                  ·
                    rfl

theorem cell20_917155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_917155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917155 prefixEnd_917155 := by exact prefixLift 917155
  have htrace : WordTrace (prefixWord ++ tailWord_917155) baseStart_917155 baseEnd_917155 := by
    simpa [prefixWord, tailWord_917155, baseEnd_917155] using wordTrace_append hprefix tailTrace_917155
  have hstable : (prefixWord ++ tailWord_917155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917155).length < 2 ^ (prefixWord ++ tailWord_917155).sum := by decide
  have hdescent : baseEnd_917155 < baseStart_917155 := by decide
  rcases family_descends (prefixWord ++ tailWord_917155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917165 : List Nat := [1, 5, 2, 1, 1, 1, 1, 5, 3]
def baseStart_917165 : Nat := 118140960795 + 917165 * 2 ^ 59
def prefixEnd_917165 : Nat := 4983230072969 + 3 ^ 40 * 917165 * 2
def baseEnd_917165 : Nat := 418619097316452730150703

theorem tailTrace_917165 : CollatzResearch.WordTrace tailWord_917165 prefixEnd_917165 418619097316452730150703 := by
  unfold tailWord_917165
  simp only [CollatzResearch.WordTrace]
  refine ⟨33451755722275319156416949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22301170481516879437611299 33451755722275319156416949)
  ·
    refine ⟨3136102098963311170914089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33451755722275319156416949 3136102098963311170914089)
    ·
      refine ⟨2352076574222483378185567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3136102098963311170914089 2352076574222483378185567)
      ·
        refine ⟨3528114861333725067278351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2352076574222483378185567 3528114861333725067278351)
        ·
          refine ⟨5292172292000587600917527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3528114861333725067278351 5292172292000587600917527)
          ·
            refine ⟨7938258438000881401376291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5292172292000587600917527 7938258438000881401376291)
            ·
              refine ⟨11907387657001322102064437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7938258438000881401376291 11907387657001322102064437)
              ·
                refine ⟨1116317592843873947068541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11907387657001322102064437 1116317592843873947068541)
                ·
                  refine ⟨418619097316452730150703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1116317592843873947068541 418619097316452730150703)
                  ·
                    rfl

theorem cell20_917165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_917165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917165 prefixEnd_917165 := by exact prefixLift 917165
  have htrace : WordTrace (prefixWord ++ tailWord_917165) baseStart_917165 baseEnd_917165 := by
    simpa [prefixWord, tailWord_917165, baseEnd_917165] using wordTrace_append hprefix tailTrace_917165
  have hstable : (prefixWord ++ tailWord_917165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917165).length < 2 ^ (prefixWord ++ tailWord_917165).sum := by decide
  have hdescent : baseEnd_917165 < baseStart_917165 := by decide
  rcases family_descends (prefixWord ++ tailWord_917165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917210 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_917210 : Nat := 118140960795 + 917210 * 2 ^ 59
def prefixEnd_917210 : Nat := 4983230072969 + 3 ^ 40 * 917210 * 2
def baseEnd_917210 : Nat := 418639636542632573650519

theorem tailTrace_917210 : CollatzResearch.WordTrace tailWord_917210 prefixEnd_917210 418639636542632573650519 := by
  unfold tailWord_917210
  simp only [CollatzResearch.WordTrace]
  refine ⟨8363349251778072960451271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22302264671408194561203389 8363349251778072960451271)
  ·
    refine ⟨12545023877667109440676907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8363349251778072960451271 12545023877667109440676907)
    ·
      refine ⟨18817535816500664161015361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12545023877667109440676907 18817535816500664161015361)
      ·
        refine ⟨14113151862375498120761521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18817535816500664161015361 14113151862375498120761521)
        ·
          refine ⟨10584863896781623590571141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14113151862375498120761521 10584863896781623590571141)
          ·
            refine ⟨1984661980646554423232089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10584863896781623590571141 1984661980646554423232089)
            ·
              refine ⟨1488496485484915817424067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1984661980646554423232089 1488496485484915817424067)
              ·
                refine ⟨2232744728227373726136101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1488496485484915817424067 2232744728227373726136101)
                ·
                  refine ⟨418639636542632573650519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2232744728227373726136101 418639636542632573650519)
                  ·
                    rfl

theorem cell20_917210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_917210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917210 prefixEnd_917210 := by exact prefixLift 917210
  have htrace : WordTrace (prefixWord ++ tailWord_917210) baseStart_917210 baseEnd_917210 := by
    simpa [prefixWord, tailWord_917210, baseEnd_917210] using wordTrace_append hprefix tailTrace_917210
  have hstable : (prefixWord ++ tailWord_917210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917210).length < 2 ^ (prefixWord ++ tailWord_917210).sum := by decide
  have hdescent : baseEnd_917210 < baseStart_917210 := by decide
  rcases family_descends (prefixWord ++ tailWord_917210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917231 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 4]
def baseStart_917231 : Nat := 118140960795 + 917231 * 2 ^ 59
def prefixEnd_917231 : Nat := 4983230072969 + 3 ^ 40 * 917231 * 2
def baseEnd_917231 : Nat := 418649221514849833950433

theorem tailTrace_917231 : CollatzResearch.WordTrace tailWord_917231 prefixEnd_917231 418649221514849833950433 := by
  unfold tailWord_917231
  simp only [CollatzResearch.WordTrace]
  refine ⟨33454162940036212428319547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22302775293357474952213031 33454162940036212428319547)
  ·
    refine ⟨50181244410054318642479321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33454162940036212428319547 50181244410054318642479321)
    ·
      refine ⟨37635933307540738981859491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50181244410054318642479321 37635933307540738981859491)
      ·
        refine ⟨56453899961311108472789237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37635933307540738981859491 56453899961311108472789237)
        ·
          refine ⟨5292553121372916419323991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56453899961311108472789237 5292553121372916419323991)
          ·
            refine ⟨7938829682059374628985987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5292553121372916419323991 7938829682059374628985987)
            ·
              refine ⟨11908244523089061943478981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7938829682059374628985987 11908244523089061943478981)
              ·
                refine ⟨2232795848079199114402309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11908244523089061943478981 2232795848079199114402309)
                ·
                  refine ⟨418649221514849833950433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2232795848079199114402309 418649221514849833950433)
                  ·
                    rfl

theorem cell20_917231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_917231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917231 prefixEnd_917231 := by exact prefixLift 917231
  have htrace : WordTrace (prefixWord ++ tailWord_917231) baseStart_917231 baseEnd_917231 := by
    simpa [prefixWord, tailWord_917231, baseEnd_917231] using wordTrace_append hprefix tailTrace_917231
  have hstable : (prefixWord ++ tailWord_917231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917231).length < 2 ^ (prefixWord ++ tailWord_917231).sum := by decide
  have hdescent : baseEnd_917231 < baseStart_917231 := by decide
  rcases family_descends (prefixWord ++ tailWord_917231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917262 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_917262 : Nat := 118140960795 + 917262 * 2 ^ 59
def prefixEnd_917262 : Nat := 4983230072969 + 3 ^ 40 * 917262 * 2
def baseEnd_917262 : Nat := 418663370759551503916973

theorem tailTrace_917262 : CollatzResearch.WordTrace tailWord_917262 prefixEnd_917262 418663370759551503916973 := by
  unfold tailWord_917262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4181911700365488090337255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22303529068615936481798693 4181911700365488090337255)
  ·
    refine ⟨6272867550548232135505883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4181911700365488090337255 6272867550548232135505883)
    ·
      refine ⟨9409301325822348203258825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6272867550548232135505883 9409301325822348203258825)
      ·
        refine ⟨7056975994366761152444119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9409301325822348203258825 7056975994366761152444119)
        ·
          refine ⟨10585463991550141728666179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7056975994366761152444119 10585463991550141728666179)
          ·
            refine ⟨15878195987325212592999269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10585463991550141728666179 15878195987325212592999269)
            ·
              refine ⟨2977161747623477361187363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15878195987325212592999269 2977161747623477361187363)
              ·
                refine ⟨4465742621435216041781045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2977161747623477361187363 4465742621435216041781045)
                ·
                  refine ⟨418663370759551503916973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4465742621435216041781045 418663370759551503916973)
                  ·
                    rfl

theorem cell20_917262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_917262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917262 prefixEnd_917262 := by exact prefixLift 917262
  have htrace : WordTrace (prefixWord ++ tailWord_917262) baseStart_917262 baseEnd_917262 := by
    simpa [prefixWord, tailWord_917262, baseEnd_917262] using wordTrace_append hprefix tailTrace_917262
  have hstable : (prefixWord ++ tailWord_917262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917262).length < 2 ^ (prefixWord ++ tailWord_917262).sum := by decide
  have hdescent : baseEnd_917262 < baseStart_917262 := by decide
  rcases family_descends (prefixWord ++ tailWord_917262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917268 : List Nat := [2, 4, 4, 1, 1, 1, 2, 5]
def baseStart_917268 : Nat := 118140960795 + 917268 * 2 ^ 59
def prefixEnd_917268 : Nat := 4983230072969 + 3 ^ 40 * 917268 * 2
def baseEnd_917268 : Nat := 139555369774347383238983

theorem tailTrace_917268 : CollatzResearch.WordTrace tailWord_917268 prefixEnd_917268 139555369774347383238983 := by
  unfold tailWord_917268
  simp only [CollatzResearch.WordTrace]
  refine ⟨16727756220451083873708229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22303674960601445164944305 16727756220451083873708229)
  ·
    refine ⟨3136454291334578226320293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16727756220451083873708229 3136454291334578226320293)
    ·
      refine ⟨588085179625233417435055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3136454291334578226320293 588085179625233417435055)
      ·
        refine ⟨882127769437850126152583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588085179625233417435055 882127769437850126152583)
        ·
          refine ⟨1323191654156775189228875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882127769437850126152583 1323191654156775189228875)
          ·
            refine ⟨1984787481235162783843313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323191654156775189228875 1984787481235162783843313)
            ·
              refine ⟨1488590610926372087882485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1984787481235162783843313 1488590610926372087882485)
              ·
                refine ⟨139555369774347383238983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1488590610926372087882485 139555369774347383238983)
                ·
                  rfl

theorem cell20_917268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 5].length) (baseStart_917268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917268 prefixEnd_917268 := by exact prefixLift 917268
  have htrace : WordTrace (prefixWord ++ tailWord_917268) baseStart_917268 baseEnd_917268 := by
    simpa [prefixWord, tailWord_917268, baseEnd_917268] using wordTrace_append hprefix tailTrace_917268
  have hstable : (prefixWord ++ tailWord_917268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917268).length < 2 ^ (prefixWord ++ tailWord_917268).sum := by decide
  have hdescent : baseEnd_917268 < baseStart_917268 := by decide
  rcases family_descends (prefixWord ++ tailWord_917268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917320 : List Nat := [2, 1, 3, 1, 1, 6, 2, 2, 2]
def baseStart_917320 : Nat := 118140960795 + 917320 * 2 ^ 59
def prefixEnd_917320 : Nat := 4983230072969 + 3 ^ 40 * 917320 * 2
def baseEnd_917320 : Nat := 418689843539961079983403

theorem tailTrace_917320 : CollatzResearch.WordTrace tailWord_917320 prefixEnd_917320 418689843539961079983403 := by
  unfold tailWord_917320
  simp only [CollatzResearch.WordTrace]
  refine ⟨16728704518356890314154707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22304939357809187085539609 16728704518356890314154707)
  ·
    refine ⟨25093056777535335471232061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16728704518356890314154707 25093056777535335471232061)
    ·
      refine ⟨9409896291575750801712023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25093056777535335471232061 9409896291575750801712023)
      ·
        refine ⟨14114844437363626202568035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9409896291575750801712023 14114844437363626202568035)
        ·
          refine ⟨21172266656045439303852053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14114844437363626202568035 21172266656045439303852053)
          ·
            refine ⟨992449999502129967368065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21172266656045439303852053 992449999502129967368065)
            ·
              refine ⟨744337499626597475526049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992449999502129967368065 744337499626597475526049)
              ·
                refine ⟨558253124719948106644537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 744337499626597475526049 558253124719948106644537)
                ·
                  refine ⟨418689843539961079983403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558253124719948106644537 418689843539961079983403)
                  ·
                    rfl

theorem cell20_917320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 2].length) (baseStart_917320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917320 prefixEnd_917320 := by exact prefixLift 917320
  have htrace : WordTrace (prefixWord ++ tailWord_917320) baseStart_917320 baseEnd_917320 := by
    simpa [prefixWord, tailWord_917320, baseEnd_917320] using wordTrace_append hprefix tailTrace_917320
  have hstable : (prefixWord ++ tailWord_917320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917320).length < 2 ^ (prefixWord ++ tailWord_917320).sum := by decide
  have hdescent : baseEnd_917320 < baseStart_917320 := by decide
  rcases family_descends (prefixWord ++ tailWord_917320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917338 : List Nat := [3, 1, 1, 2, 1, 3, 1, 5, 3]
def baseStart_917338 : Nat := 118140960795 + 917338 * 2 ^ 59
def prefixEnd_917338 : Nat := 4983230072969 + 3 ^ 40 * 917338 * 2
def baseEnd_917338 : Nat := 418698059230433017383329

theorem tailTrace_917338 : CollatzResearch.WordTrace tailWord_917338 prefixEnd_917338 418698059230433017383329 := by
  unfold tailWord_917338
  simp only [CollatzResearch.WordTrace]
  refine ⟨8364516387662142425616167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22305377033765713134976445 8364516387662142425616167)
  ·
    refine ⟨12546774581493213638424251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8364516387662142425616167 12546774581493213638424251)
    ·
      refine ⟨18820161872239820457636377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12546774581493213638424251 18820161872239820457636377)
      ·
        refine ⟨14115121404179865343227283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18820161872239820457636377 14115121404179865343227283)
        ·
          refine ⟨21172682106269798014840925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14115121404179865343227283 21172682106269798014840925)
          ·
            refine ⟨7939755789851174255565347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21172682106269798014840925 7939755789851174255565347)
            ·
              refine ⟨11909633684776761383348021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7939755789851174255565347 11909633684776761383348021)
              ·
                refine ⟨1116528157947821379688877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11909633684776761383348021 1116528157947821379688877)
                ·
                  refine ⟨418698059230433017383329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1116528157947821379688877 418698059230433017383329)
                  ·
                    rfl

theorem cell20_917338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_917338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917338 prefixEnd_917338 := by exact prefixLift 917338
  have htrace : WordTrace (prefixWord ++ tailWord_917338) baseStart_917338 baseEnd_917338 := by
    simpa [prefixWord, tailWord_917338, baseEnd_917338] using wordTrace_append hprefix tailTrace_917338
  have hstable : (prefixWord ++ tailWord_917338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917338).length < 2 ^ (prefixWord ++ tailWord_917338).sum := by decide
  have hdescent : baseEnd_917338 < baseStart_917338 := by decide
  rcases family_descends (prefixWord ++ tailWord_917338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917345 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 4]
def baseStart_917345 : Nat := 118140960795 + 917345 * 2 ^ 59
def prefixEnd_917345 : Nat := 4983230072969 + 3 ^ 40 * 917345 * 2
def baseEnd_917345 : Nat := 418701254221172104149967

theorem tailTrace_917345 : CollatzResearch.WordTrace tailWord_917345 prefixEnd_917345 418701254221172104149967 := by
  unfold tailWord_917345
  simp only [CollatzResearch.WordTrace]
  refine ⟨33458320861623209897969489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22305547241082139931979659 33458320861623209897969489)
  ·
    refine ⟨25093740646217407423477117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33458320861623209897969489 25093740646217407423477117)
    ·
      refine ⟨9410152742331527783803919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25093740646217407423477117 9410152742331527783803919)
      ·
        refine ⟨14115229113497291675705879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9410152742331527783803919 14115229113497291675705879)
        ·
          refine ⟨21172843670245937513558819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14115229113497291675705879 21172843670245937513558819)
          ·
            refine ⟨31759265505368906270338229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21172843670245937513558819 31759265505368906270338229)
            ·
              refine ⟨2977431141128334962844209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31759265505368906270338229 2977431141128334962844209)
              ·
                refine ⟨2233073355846251222133157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2977431141128334962844209 2233073355846251222133157)
                ·
                  refine ⟨418701254221172104149967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2233073355846251222133157 418701254221172104149967)
                  ·
                    rfl

theorem cell20_917345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_917345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917345 prefixEnd_917345 := by exact prefixLift 917345
  have htrace : WordTrace (prefixWord ++ tailWord_917345) baseStart_917345 baseEnd_917345 := by
    simpa [prefixWord, tailWord_917345, baseEnd_917345] using wordTrace_append hprefix tailTrace_917345
  have hstable : (prefixWord ++ tailWord_917345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917345).length < 2 ^ (prefixWord ++ tailWord_917345).sum := by decide
  have hdescent : baseEnd_917345 < baseStart_917345 := by decide
  rcases family_descends (prefixWord ++ tailWord_917345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917348 : List Nat := [2, 3, 1, 1, 5, 1, 3, 4]
def baseStart_917348 : Nat := 118140960795 + 917348 * 2 ^ 59
def prefixEnd_917348 : Nat := 4983230072969 + 3 ^ 40 * 917348 * 2
def baseEnd_917348 : Nat := 139567541167639142349985

theorem tailTrace_917348 : CollatzResearch.WordTrace tailWord_917348 prefixEnd_917348 139567541167639142349985 := by
  unfold tailWord_917348
  simp only [CollatzResearch.WordTrace]
  refine ⟨16729215140306170705164349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22305620187074894273552465 16729215140306170705164349)
  ·
    refine ⟨6273455677614814014436631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16729215140306170705164349 6273455677614814014436631)
    ·
      refine ⟨9410183516422221021654947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6273455677614814014436631 9410183516422221021654947)
      ·
        refine ⟨14115275274633331532482421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9410183516422221021654947 14115275274633331532482421)
        ·
          refine ⟨1323307056996874831170227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14115275274633331532482421 1323307056996874831170227)
          ·
            refine ⟨1984960585495312246755341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323307056996874831170227 1984960585495312246755341)
            ·
              refine ⟨744360219560742092533253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1984960585495312246755341 744360219560742092533253)
              ·
                refine ⟨139567541167639142349985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 744360219560742092533253 139567541167639142349985)
                ·
                  rfl

theorem cell20_917348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_917348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917348 prefixEnd_917348 := by exact prefixLift 917348
  have htrace : WordTrace (prefixWord ++ tailWord_917348) baseStart_917348 baseEnd_917348 := by
    simpa [prefixWord, tailWord_917348, baseEnd_917348] using wordTrace_append hprefix tailTrace_917348
  have hstable : (prefixWord ++ tailWord_917348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917348).length < 2 ^ (prefixWord ++ tailWord_917348).sum := by decide
  have hdescent : baseEnd_917348 < baseStart_917348 := by decide
  rcases family_descends (prefixWord ++ tailWord_917348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917358 : List Nat := [4, 1, 2, 3, 1, 2, 2, 3, 2]
def baseStart_917358 : Nat := 118140960795 + 917358 * 2 ^ 59
def prefixEnd_917358 : Nat := 4983230072969 + 3 ^ 40 * 917358 * 2
def baseEnd_917358 : Nat := 418707187775401836716581

theorem tailTrace_917358 : CollatzResearch.WordTrace tailWord_917358 prefixEnd_917358 418707187775401836716581 := by
  unfold tailWord_917358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4182349376322014139774091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22305863340384075412128485 4182349376322014139774091)
  ·
    refine ⟨6273524064483021209661137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4182349376322014139774091 6273524064483021209661137)
    ·
      refine ⟨4705143048362265907245853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6273524064483021209661137 4705143048362265907245853)
      ·
        refine ⟨1764428643135849715217195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4705143048362265907245853 1764428643135849715217195)
        ·
          refine ⟨2646642964703774572825793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1764428643135849715217195 2646642964703774572825793)
          ·
            refine ⟨1984982223527830929619345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2646642964703774572825793 1984982223527830929619345)
            ·
              refine ⟨1488736667645873197214509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1984982223527830929619345 1488736667645873197214509)
              ·
                refine ⟨558276250367202448955441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1488736667645873197214509 558276250367202448955441)
                ·
                  refine ⟨418707187775401836716581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558276250367202448955441 418707187775401836716581)
                  ·
                    rfl

theorem cell20_917358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_917358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917358 prefixEnd_917358 := by exact prefixLift 917358
  have htrace : WordTrace (prefixWord ++ tailWord_917358) baseStart_917358 baseEnd_917358 := by
    simpa [prefixWord, tailWord_917358, baseEnd_917358] using wordTrace_append hprefix tailTrace_917358
  have hstable : (prefixWord ++ tailWord_917358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917358).length < 2 ^ (prefixWord ++ tailWord_917358).sum := by decide
  have hdescent : baseEnd_917358 < baseStart_917358 := by decide
  rcases family_descends (prefixWord ++ tailWord_917358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917407 : List Nat := [1, 1, 2, 5, 3, 1, 1, 6]
def baseStart_917407 : Nat := 118140960795 + 917407 * 2 ^ 59
def prefixEnd_917407 : Nat := 4983230072969 + 3 ^ 40 * 917407 * 2
def baseEnd_917407 : Nat := 139576517570191814694349

theorem tailTrace_917407 : CollatzResearch.WordTrace tailWord_917407 prefixEnd_917407 139576517570191814694349 := by
  unfold tailWord_917407
  simp only [CollatzResearch.WordTrace]
  refine ⟨33460582187398594486726475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22307054791599062991150983 33460582187398594486726475)
  ·
    refine ⟨50190873281097891730089713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33460582187398594486726475 50190873281097891730089713)
    ·
      refine ⟨37643154960823418797567285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50190873281097891730089713 37643154960823418797567285)
      ·
        refine ⟨3529045777577195512271933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37643154960823418797567285 3529045777577195512271933)
        ·
          refine ⟨1323392166591448317101975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3529045777577195512271933 1323392166591448317101975)
          ·
            refine ⟨1985088249887172475652963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323392166591448317101975 1985088249887172475652963)
            ·
              refine ⟨2977632374830758713479445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1985088249887172475652963 2977632374830758713479445)
              ·
                refine ⟨139576517570191814694349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2977632374830758713479445 139576517570191814694349)
                ·
                  rfl

theorem cell20_917407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 6].length) (baseStart_917407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917407 prefixEnd_917407 := by exact prefixLift 917407
  have htrace : WordTrace (prefixWord ++ tailWord_917407) baseStart_917407 baseEnd_917407 := by
    simpa [prefixWord, tailWord_917407, baseEnd_917407] using wordTrace_append hprefix tailTrace_917407
  have hstable : (prefixWord ++ tailWord_917407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917407).length < 2 ^ (prefixWord ++ tailWord_917407).sum := by decide
  have hdescent : baseEnd_917407 < baseStart_917407 := by decide
  rcases family_descends (prefixWord ++ tailWord_917407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917438 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_917438 : Nat := 118140960795 + 917438 * 2 ^ 59
def prefixEnd_917438 : Nat := 4983230072969 + 3 ^ 40 * 917438 * 2
def baseEnd_917438 : Nat := 418743701955277114049587

theorem tailTrace_917438 : CollatzResearch.WordTrace tailWord_917438 prefixEnd_917438 418743701955277114049587 := by
  unfold tailWord_917438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4182714106285785847638121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22307808566857524520736645 4182714106285785847638121)
  ·
    refine ⟨3137035579714339385728591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4182714106285785847638121 3137035579714339385728591)
    ·
      refine ⟨4705553369571509078592887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3137035579714339385728591 4705553369571509078592887)
      ·
        refine ⟨7058330054357263617889331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4705553369571509078592887 7058330054357263617889331)
        ·
          refine ⟨10587495081535895426833997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7058330054357263617889331 10587495081535895426833997)
          ·
            refine ⟨3970310655575960785062749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10587495081535895426833997 3970310655575960785062749)
            ·
              refine ⟨1488866495840985294398531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3970310655575960785062749 1488866495840985294398531)
              ·
                refine ⟨2233299743761477941597797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1488866495840985294398531 2233299743761477941597797)
                ·
                  refine ⟨418743701955277114049587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2233299743761477941597797 418743701955277114049587)
                  ·
                    rfl

theorem cell20_917438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_917438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917438 prefixEnd_917438 := by exact prefixLift 917438
  have htrace : WordTrace (prefixWord ++ tailWord_917438) baseStart_917438 baseEnd_917438 := by
    simpa [prefixWord, tailWord_917438, baseEnd_917438] using wordTrace_append hprefix tailTrace_917438
  have hstable : (prefixWord ++ tailWord_917438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917438).length < 2 ^ (prefixWord ++ tailWord_917438).sum := by decide
  have hdescent : baseEnd_917438 < baseStart_917438 := by decide
  rcases family_descends (prefixWord ++ tailWord_917438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917448 : List Nat := [2, 1, 3, 1, 4, 3, 2, 1, 3]
def baseStart_917448 : Nat := 118140960795 + 917448 * 2 ^ 59
def prefixEnd_917448 : Nat := 4983230072969 + 3 ^ 40 * 917448 * 2
def baseEnd_917448 : Nat := 418748266227761523716213

theorem tailTrace_917448 : CollatzResearch.WordTrace tailWord_917448 prefixEnd_917448 418748266227761523716213 := by
  unfold tailWord_917448
  simp only [CollatzResearch.WordTrace]
  refine ⟨16731038790125029244484499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22308051720166705659312665 16731038790125029244484499)
  ·
    refine ⟨25096558185187543866726749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16731038790125029244484499 25096558185187543866726749)
    ·
      refine ⟨9411209319445328950022531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25096558185187543866726749 9411209319445328950022531)
      ·
        refine ⟨14116813979167993425033797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9411209319445328950022531 14116813979167993425033797)
        ·
          refine ⟨2646902621093998767193837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14116813979167993425033797 2646902621093998767193837)
          ·
            refine ⟨992588482910249537697689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2646902621093998767193837 992588482910249537697689)
            ·
              refine ⟨744441362182687153273267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992588482910249537697689 744441362182687153273267)
              ·
                refine ⟨1116662043274030729909901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744441362182687153273267 1116662043274030729909901)
                ·
                  refine ⟨418748266227761523716213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1116662043274030729909901 418748266227761523716213)
                  ·
                    rfl

theorem cell20_917448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 3].length) (baseStart_917448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917448 prefixEnd_917448 := by exact prefixLift 917448
  have htrace : WordTrace (prefixWord ++ tailWord_917448) baseStart_917448 baseEnd_917448 := by
    simpa [prefixWord, tailWord_917448, baseEnd_917448] using wordTrace_append hprefix tailTrace_917448
  have hstable : (prefixWord ++ tailWord_917448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917448).length < 2 ^ (prefixWord ++ tailWord_917448).sum := by decide
  have hdescent : baseEnd_917448 < baseStart_917448 := by decide
  rcases family_descends (prefixWord ++ tailWord_917448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917473 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 7]
def baseStart_917473 : Nat := 118140960795 + 917473 * 2 ^ 59
def prefixEnd_917473 : Nat := 4983230072969 + 3 ^ 40 * 917473 * 2
def baseEnd_917473 : Nat := 418759676908972547882777

theorem tailTrace_917473 : CollatzResearch.WordTrace tailWord_917473 prefixEnd_917473 418759676908972547882777 := by
  unfold tailWord_917473
  simp only [CollatzResearch.WordTrace]
  refine ⟨33462989405159487758629073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22308659603439658505752715 33462989405159487758629073)
  ·
    refine ⟨25097242053869615818971805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33462989405159487758629073 25097242053869615818971805)
    ·
      refine ⟨9411465770201105932114427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25097242053869615818971805 9411465770201105932114427)
      ·
        refine ⟨14117198655301658898171641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9411465770201105932114427 14117198655301658898171641)
        ·
          refine ⟨10587898991476244173628731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14117198655301658898171641 10587898991476244173628731)
          ·
            refine ⟨15881848487214366260443097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10587898991476244173628731 15881848487214366260443097)
            ·
              refine ⟨11911386365410774695332323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15881848487214366260443097 11911386365410774695332323)
              ·
                refine ⟨17867079548116162042998485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11911386365410774695332323 17867079548116162042998485)
                ·
                  refine ⟨418759676908972547882777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17867079548116162042998485 418759676908972547882777)
                  ·
                    rfl

theorem cell20_917473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_917473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917473 prefixEnd_917473 := by exact prefixLift 917473
  have htrace : WordTrace (prefixWord ++ tailWord_917473) baseStart_917473 baseEnd_917473 := by
    simpa [prefixWord, tailWord_917473, baseEnd_917473] using wordTrace_append hprefix tailTrace_917473
  have hstable : (prefixWord ++ tailWord_917473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917473).length < 2 ^ (prefixWord ++ tailWord_917473).sum := by decide
  have hdescent : baseEnd_917473 < baseStart_917473 := by decide
  rcases family_descends (prefixWord ++ tailWord_917473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917476 : List Nat := [2, 3, 1, 1, 1, 1, 4, 5, 2]
def baseStart_917476 : Nat := 118140960795 + 917476 * 2 ^ 59
def prefixEnd_917476 : Nat := 4983230072969 + 3 ^ 40 * 917476 * 2
def baseEnd_917476 : Nat := 418761046190717870782765

theorem tailTrace_917476 : CollatzResearch.WordTrace tailWord_917476 prefixEnd_917476 418761046190717870782765 := by
  unfold tailWord_917476
  simp only [CollatzResearch.WordTrace]
  refine ⟨16731549412074309635494141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22308732549432412847325521 16731549412074309635494141)
  ·
    refine ⟨6274331029527866113310303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16731549412074309635494141 6274331029527866113310303)
    ·
      refine ⟨9411496544291799169965455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6274331029527866113310303 9411496544291799169965455)
      ·
        refine ⟨14117244816437698754948183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9411496544291799169965455 14117244816437698754948183)
        ·
          refine ⟨21175867224656548132422275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14117244816437698754948183 21175867224656548132422275)
          ·
            refine ⟨31763800836984822198633413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21175867224656548132422275 31763800836984822198633413)
            ·
              refine ⟨5955712656934654162243765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31763800836984822198633413 5955712656934654162243765)
              ·
                refine ⟨558348061587623827710353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5955712656934654162243765 558348061587623827710353)
                ·
                  refine ⟨418761046190717870782765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558348061587623827710353 418761046190717870782765)
                  ·
                    rfl

theorem cell20_917476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_917476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917476 prefixEnd_917476 := by exact prefixLift 917476
  have htrace : WordTrace (prefixWord ++ tailWord_917476) baseStart_917476 baseEnd_917476 := by
    simpa [prefixWord, tailWord_917476, baseEnd_917476] using wordTrace_append hprefix tailTrace_917476
  have hstable : (prefixWord ++ tailWord_917476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917476).length < 2 ^ (prefixWord ++ tailWord_917476).sum := by decide
  have hdescent : baseEnd_917476 < baseStart_917476 := by decide
  rcases family_descends (prefixWord ++ tailWord_917476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917489 : List Nat := [1, 2, 2, 2, 6, 1, 2, 2, 2]
def baseStart_917489 : Nat := 118140960795 + 917489 * 2 ^ 59
def prefixEnd_917489 : Nat := 4983230072969 + 3 ^ 40 * 917489 * 2
def baseEnd_917489 : Nat := 418766979744947603349379

theorem tailTrace_917489 : CollatzResearch.WordTrace tailWord_917489 prefixEnd_917489 418766979744947603349379 := by
  unfold tailWord_917489
  simp only [CollatzResearch.WordTrace]
  refine ⟨33463572973101522491211521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22309048648734348327474347 33463572973101522491211521)
  ·
    refine ⟨25097679729826141868408641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33463572973101522491211521 25097679729826141868408641)
    ·
      refine ⟨18823259797369606401306481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25097679729826141868408641 18823259797369606401306481)
      ·
        refine ⟨14117444848027204800979861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18823259797369606401306481 14117444848027204800979861)
        ·
          refine ⟨661755227251275225045931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14117444848027204800979861 661755227251275225045931)
          ·
            refine ⟨992632840876912837568897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661755227251275225045931 992632840876912837568897)
            ·
              refine ⟨744474630657684628176673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992632840876912837568897 744474630657684628176673)
              ·
                refine ⟨558355972993263471132505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 744474630657684628176673 558355972993263471132505)
                ·
                  refine ⟨418766979744947603349379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558355972993263471132505 418766979744947603349379)
                  ·
                    rfl

theorem cell20_917489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 2].length) (baseStart_917489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917489 prefixEnd_917489 := by exact prefixLift 917489
  have htrace : WordTrace (prefixWord ++ tailWord_917489) baseStart_917489 baseEnd_917489 := by
    simpa [prefixWord, tailWord_917489, baseEnd_917489] using wordTrace_append hprefix tailTrace_917489
  have hstable : (prefixWord ++ tailWord_917489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917489).length < 2 ^ (prefixWord ++ tailWord_917489).sum := by decide
  have hdescent : baseEnd_917489 < baseStart_917489 := by decide
  rcases family_descends (prefixWord ++ tailWord_917489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917514 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 4]
def baseStart_917514 : Nat := 118140960795 + 917514 * 2 ^ 59
def prefixEnd_917514 : Nat := 4983230072969 + 3 ^ 40 * 917514 * 2
def baseEnd_917514 : Nat := 418778390426158627515943

theorem tailTrace_917514 : CollatzResearch.WordTrace tailWord_917514 prefixEnd_917514 418778390426158627515943 := by
  unfold tailWord_917514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8366121199502737940217899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22309656532007301173914397 8366121199502737940217899)
  ·
    refine ⟨12549181799254106910326849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8366121199502737940217899 12549181799254106910326849)
    ·
      refine ⟨9411886349440580182745137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12549181799254106910326849 9411886349440580182745137)
      ·
        refine ⟨7058914762080435137058853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9411886349440580182745137 7058914762080435137058853)
        ·
          refine ⟨1323546517890081588198535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7058914762080435137058853 1323546517890081588198535)
          ·
            refine ⟨1985319776835122382297803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323546517890081588198535 1985319776835122382297803)
            ·
              refine ⟨2977979665252683573446705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1985319776835122382297803 2977979665252683573446705)
              ·
                refine ⟨2233484748939512680085029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2977979665252683573446705 2233484748939512680085029)
                ·
                  refine ⟨418778390426158627515943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2233484748939512680085029 418778390426158627515943)
                  ·
                    rfl

theorem cell20_917514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_917514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917514 prefixEnd_917514 := by exact prefixLift 917514
  have htrace : WordTrace (prefixWord ++ tailWord_917514) baseStart_917514 baseEnd_917514 := by
    simpa [prefixWord, tailWord_917514, baseEnd_917514] using wordTrace_append hprefix tailTrace_917514
  have hstable : (prefixWord ++ tailWord_917514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917514).length < 2 ^ (prefixWord ++ tailWord_917514).sum := by decide
  have hdescent : baseEnd_917514 < baseStart_917514 := by decide
  rcases family_descends (prefixWord ++ tailWord_917514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917552 : List Nat := [2, 1, 1, 1, 2, 5, 2, 4, 2]
def baseStart_917552 : Nat := 118140960795 + 917552 * 2 ^ 59
def prefixEnd_917552 : Nat := 4983230072969 + 3 ^ 40 * 917552 * 2
def baseEnd_917552 : Nat := 418795734661599384249121

theorem tailTrace_917552 : CollatzResearch.WordTrace tailWord_917552 prefixEnd_917552 418795734661599384249121 := by
  unfold tailWord_917552
  simp only [CollatzResearch.WordTrace]
  refine ⟨16732935385936642125377455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22310580514582189500503273 16732935385936642125377455)
  ·
    refine ⟨25099403078904963188066183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16732935385936642125377455 25099403078904963188066183)
    ·
      refine ⟨37649104618357444782099275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25099403078904963188066183 37649104618357444782099275)
      ·
        refine ⟨56473656927536167173148913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37649104618357444782099275 56473656927536167173148913)
        ·
          refine ⟨42355242695652125379861685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56473656927536167173148913 42355242695652125379861685)
          ·
            refine ⟨3970804002717386754362033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42355242695652125379861685 3970804002717386754362033)
            ·
              refine ⟨2978103002038040065771525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3970804002717386754362033 2978103002038040065771525)
              ·
                refine ⟨558394312882132512332161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2978103002038040065771525 558394312882132512332161)
                ·
                  refine ⟨418795734661599384249121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558394312882132512332161 418795734661599384249121)
                  ·
                    rfl

theorem cell20_917552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 2].length) (baseStart_917552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917552 prefixEnd_917552 := by exact prefixLift 917552
  have htrace : WordTrace (prefixWord ++ tailWord_917552) baseStart_917552 baseEnd_917552 := by
    simpa [prefixWord, tailWord_917552, baseEnd_917552] using wordTrace_append hprefix tailTrace_917552
  have hstable : (prefixWord ++ tailWord_917552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917552).length < 2 ^ (prefixWord ++ tailWord_917552).sum := by decide
  have hdescent : baseEnd_917552 < baseStart_917552 := by decide
  rcases family_descends (prefixWord ++ tailWord_917552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917586 : List Nat := [3, 2, 2, 1, 4, 2, 1, 3, 2]
def baseStart_917586 : Nat := 118140960795 + 917586 * 2 ^ 59
def prefixEnd_917586 : Nat := 4983230072969 + 3 ^ 40 * 917586 * 2
def baseEnd_917586 : Nat := 418811253188046377115649

theorem tailTrace_917586 : CollatzResearch.WordTrace tailWord_917586 prefixEnd_917586 418811253188046377115649 := by
  unfold tailWord_917586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8366777713437527014373153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22311407235833405371661741 8366777713437527014373153)
  ·
    refine ⟨6275083285078145260779865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8366777713437527014373153 6275083285078145260779865)
    ·
      refine ⟨4706312463808608945584899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6275083285078145260779865 4706312463808608945584899)
      ·
        refine ⟨7059468695712913418377349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4706312463808608945584899 7059468695712913418377349)
        ·
          refine ⟨1323650380446171265945753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7059468695712913418377349 1323650380446171265945753)
          ·
            refine ⟨992737785334628449459315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1323650380446171265945753 992737785334628449459315)
            ·
              refine ⟨1489106678001942674188973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992737785334628449459315 1489106678001942674188973)
              ·
                refine ⟨558415004250728502820865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1489106678001942674188973 558415004250728502820865)
                ·
                  refine ⟨418811253188046377115649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558415004250728502820865 418811253188046377115649)
                  ·
                    rfl

theorem cell20_917586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_917586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917586 prefixEnd_917586 := by exact prefixLift 917586
  have htrace : WordTrace (prefixWord ++ tailWord_917586) baseStart_917586 baseEnd_917586 := by
    simpa [prefixWord, tailWord_917586, baseEnd_917586] using wordTrace_append hprefix tailTrace_917586
  have hstable : (prefixWord ++ tailWord_917586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917586).length < 2 ^ (prefixWord ++ tailWord_917586).sum := by decide
  have hdescent : baseEnd_917586 < baseStart_917586 := by decide
  rcases family_descends (prefixWord ++ tailWord_917586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917597 : List Nat := [1, 4, 4, 1, 1, 1, 8]
def baseStart_917597 : Nat := 118140960795 + 917597 * 2 ^ 59
def prefixEnd_917597 : Nat := 4983230072969 + 3 ^ 40 * 917597 * 2
def baseEnd_917597 : Nat := 46535141543086580860993

theorem tailTrace_917597 : CollatzResearch.WordTrace tailWord_917597 prefixEnd_917597 46535141543086580860993 := by
  unfold tailWord_917597
  simp only [CollatzResearch.WordTrace]
  refine ⟨33467512056710256936143045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22311674704473504624095363 33467512056710256936143045)
  ·
    refine ⟨6275158510633173175526821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33467512056710256936143045 6275158510633173175526821)
    ·
      refine ⟨1176592220743719970411279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6275158510633173175526821 1176592220743719970411279)
      ·
        refine ⟨1764888331115579955616919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176592220743719970411279 1764888331115579955616919)
        ·
          refine ⟨2647332496673369933425379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1764888331115579955616919 2647332496673369933425379)
          ·
            refine ⟨3970998745010054900138069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647332496673369933425379 3970998745010054900138069)
            ·
              refine ⟨46535141543086580860993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3970998745010054900138069 46535141543086580860993)
              ·
                rfl

theorem cell20_917597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 8].length) (baseStart_917597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917597 prefixEnd_917597 := by exact prefixLift 917597
  have htrace : WordTrace (prefixWord ++ tailWord_917597) baseStart_917597 baseEnd_917597 := by
    simpa [prefixWord, tailWord_917597, baseEnd_917597] using wordTrace_append hprefix tailTrace_917597
  have hstable : (prefixWord ++ tailWord_917597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917597).length < 2 ^ (prefixWord ++ tailWord_917597).sum := by decide
  have hdescent : baseEnd_917597 < baseStart_917597 := by decide
  rcases family_descends (prefixWord ++ tailWord_917597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917607 : List Nat := [1, 1, 5, 1, 1, 2, 5, 2, 2]
def baseStart_917607 : Nat := 118140960795 + 917607 * 2 ^ 59
def prefixEnd_917607 : Nat := 4983230072969 + 3 ^ 40 * 917607 * 2
def baseEnd_917607 : Nat := 418820838160263637415563

theorem tailTrace_917607 : CollatzResearch.WordTrace tailWord_917607 prefixEnd_917607 418820838160263637415563 := by
  unfold tailWord_917607
  simp only [CollatzResearch.WordTrace]
  refine ⟨33467876786674028644007075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22311917857782685762671383 33467876786674028644007075)
  ·
    refine ⟨50201815180011042966010613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33467876786674028644007075 50201815180011042966010613)
    ·
      refine ⟨4706420173126035278063495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50201815180011042966010613 4706420173126035278063495)
      ·
        refine ⟨7059630259689052917095243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4706420173126035278063495 7059630259689052917095243)
        ·
          refine ⟨10589445389533579375642865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7059630259689052917095243 10589445389533579375642865)
          ·
            refine ⟨7942084042150184531732149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10589445389533579375642865 7942084042150184531732149)
            ·
              refine ⟨744570378951579799849889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7942084042150184531732149 744570378951579799849889)
              ·
                refine ⟨558427784213684849887417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 744570378951579799849889 558427784213684849887417)
                ·
                  refine ⟨418820838160263637415563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558427784213684849887417 418820838160263637415563)
                  ·
                    rfl

theorem cell20_917607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 2].length) (baseStart_917607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917607 prefixEnd_917607 := by exact prefixLift 917607
  have htrace : WordTrace (prefixWord ++ tailWord_917607) baseStart_917607 baseEnd_917607 := by
    simpa [prefixWord, tailWord_917607, baseEnd_917607] using wordTrace_append hprefix tailTrace_917607
  have hstable : (prefixWord ++ tailWord_917607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917607).length < 2 ^ (prefixWord ++ tailWord_917607).sum := by decide
  have hdescent : baseEnd_917607 < baseStart_917607 := by decide
  rcases family_descends (prefixWord ++ tailWord_917607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917618 : List Nat := [3, 2, 1, 2, 2, 2, 1, 7]
def baseStart_917618 : Nat := 118140960795 + 917618 * 2 ^ 59
def prefixEnd_917618 : Nat := 4983230072969 + 3 ^ 40 * 917618 * 2
def baseEnd_917618 : Nat := 139608619619998829349617

theorem tailTrace_917618 : CollatzResearch.WordTrace tailWord_917618 prefixEnd_917618 139608619619998829349617 := by
  unfold tailWord_917618
  simp only [CollatzResearch.WordTrace]
  refine ⟨8367069497408544380664377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22312185326422785015105005 8367069497408544380664377)
  ·
    refine ⟨6275302123056408285498283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8367069497408544380664377 6275302123056408285498283)
    ·
      refine ⟨9412953184584612428247425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6275302123056408285498283 9412953184584612428247425)
      ·
        refine ⟨7059714888438459321185569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9412953184584612428247425 7059714888438459321185569)
        ·
          refine ⟨5294786166328844490889177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7059714888438459321185569 5294786166328844490889177)
          ·
            refine ⟨3971089624746633368166883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5294786166328844490889177 3971089624746633368166883)
            ·
              refine ⟨5956634437119950052250325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3971089624746633368166883 5956634437119950052250325)
              ·
                refine ⟨139608619619998829349617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5956634437119950052250325 139608619619998829349617)
                ·
                  rfl

theorem cell20_917618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_917618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917618 prefixEnd_917618 := by exact prefixLift 917618
  have htrace : WordTrace (prefixWord ++ tailWord_917618) baseStart_917618 baseEnd_917618 := by
    simpa [prefixWord, tailWord_917618, baseEnd_917618] using wordTrace_append hprefix tailTrace_917618
  have hstable : (prefixWord ++ tailWord_917618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917618).length < 2 ^ (prefixWord ++ tailWord_917618).sum := by decide
  have hdescent : baseEnd_917618 < baseStart_917618 := by decide
  rcases family_descends (prefixWord ++ tailWord_917618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917632 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 6]
def baseStart_917632 : Nat := 118140960795 + 917632 * 2 ^ 59
def prefixEnd_917632 : Nat := 4983230072969 + 3 ^ 40 * 917632 * 2
def baseEnd_917632 : Nat := 418832248841474661582127

theorem tailTrace_917632 : CollatzResearch.WordTrace tailWord_917632 prefixEnd_917632 418832248841474661582127 := by
  unfold tailWord_917632
  simp only [CollatzResearch.WordTrace]
  refine ⟨16734394305791728956833575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22312525741055638609111433 16734394305791728956833575)
  ·
    refine ⟨25101591458687593435250363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16734394305791728956833575 25101591458687593435250363)
    ·
      refine ⟨37652387188031390152875545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25101591458687593435250363 37652387188031390152875545)
      ·
        refine ⟨28239290391023542614656659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37652387188031390152875545 28239290391023542614656659)
        ·
          refine ⟨42358935586535313921984989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28239290391023542614656659 42358935586535313921984989)
          ·
            refine ⟨15884600844950742720744371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42358935586535313921984989 15884600844950742720744371)
            ·
              refine ⟨23826901267426114081116557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15884600844950742720744371 23826901267426114081116557)
              ·
                refine ⟨8935087975284792780418709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23826901267426114081116557 8935087975284792780418709)
                ·
                  refine ⟨418832248841474661582127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8935087975284792780418709 418832248841474661582127)
                  ·
                    rfl

theorem cell20_917632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_917632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917632 prefixEnd_917632 := by exact prefixLift 917632
  have htrace : WordTrace (prefixWord ++ tailWord_917632) baseStart_917632 baseEnd_917632 := by
    simpa [prefixWord, tailWord_917632, baseEnd_917632] using wordTrace_append hprefix tailTrace_917632
  have hstable : (prefixWord ++ tailWord_917632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917632).length < 2 ^ (prefixWord ++ tailWord_917632).sum := by decide
  have hdescent : baseEnd_917632 < baseStart_917632 := by decide
  rcases family_descends (prefixWord ++ tailWord_917632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917652 : List Nat := [2, 4, 2, 3, 2, 7]
def baseStart_917652 : Nat := 118140960795 + 917652 * 2 ^ 59
def prefixEnd_917652 : Nat := 4983230072969 + 3 ^ 40 * 917652 * 2
def baseEnd_917652 : Nat := 15512643606905314107977

theorem tailTrace_917652 : CollatzResearch.WordTrace tailWord_917652 prefixEnd_917652 15512643606905314107977 := by
  unfold tailWord_917652
  simp only [CollatzResearch.WordTrace]
  refine ⟨16734759035755500664697605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22313012047674000886263473 16734759035755500664697605)
  ·
    refine ⟨3137767319204156374630801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16734759035755500664697605 3137767319204156374630801)
    ·
      refine ⟨2353325489403117280973101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3137767319204156374630801 2353325489403117280973101)
      ·
        refine ⟨882497058526168980364913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2353325489403117280973101 882497058526168980364913)
        ·
          refine ⟨661872793894626735273685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 882497058526168980364913 661872793894626735273685)
          ·
            refine ⟨15512643606905314107977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 661872793894626735273685 15512643606905314107977)
            ·
              rfl

theorem cell20_917652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 7].length) (baseStart_917652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917652 prefixEnd_917652 := by exact prefixLift 917652
  have htrace : WordTrace (prefixWord ++ tailWord_917652) baseStart_917652 baseEnd_917652 := by
    simpa [prefixWord, tailWord_917652, baseEnd_917652] using wordTrace_append hprefix tailTrace_917652
  have hstable : (prefixWord ++ tailWord_917652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917652).length < 2 ^ (prefixWord ++ tailWord_917652).sum := by decide
  have hdescent : baseEnd_917652 < baseStart_917652 := by decide
  rcases family_descends (prefixWord ++ tailWord_917652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917654 : List Nat := [5, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_917654 : Nat := 118140960795 + 917654 * 2 ^ 59
def prefixEnd_917654 : Nat := 4983230072969 + 3 ^ 40 * 917654 * 2
def baseEnd_917654 : Nat := 418842290240940362848705

theorem tailTrace_917654 : CollatzResearch.WordTrace tailWord_917654 prefixEnd_917654 418842290240940362848705 := by
  unfold tailWord_917654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2091849438593984729435501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22313060678335837113978677 2091849438593984729435501)
  ·
    refine ⟨784443539472744273538313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2091849438593984729435501 784443539472744273538313)
    ·
      refine ⟨588332654604558205153735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 784443539472744273538313 588332654604558205153735)
      ·
        refine ⟨882498981906837307730603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588332654604558205153735 882498981906837307730603)
        ·
          refine ⟨1323748472860255961595905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882498981906837307730603 1323748472860255961595905)
          ·
            refine ⟨992811354645191971196929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1323748472860255961595905 992811354645191971196929)
            ·
              refine ⟨744608515983893978397697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992811354645191971196929 744608515983893978397697)
              ·
                refine ⟨558456386987920483798273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 744608515983893978397697 558456386987920483798273)
                ·
                  refine ⟨418842290240940362848705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558456386987920483798273 418842290240940362848705)
                  ·
                    rfl

theorem cell20_917654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_917654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917654 prefixEnd_917654 := by exact prefixLift 917654
  have htrace : WordTrace (prefixWord ++ tailWord_917654) baseStart_917654 baseEnd_917654 := by
    simpa [prefixWord, tailWord_917654, baseEnd_917654] using wordTrace_append hprefix tailTrace_917654
  have hstable : (prefixWord ++ tailWord_917654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917654).length < 2 ^ (prefixWord ++ tailWord_917654).sum := by decide
  have hdescent : baseEnd_917654 < baseStart_917654 := by decide
  rcases family_descends (prefixWord ++ tailWord_917654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917656 : List Nat := [2, 1, 2, 4, 3, 8]
def baseStart_917656 : Nat := 118140960795 + 917656 * 2 ^ 59
def prefixEnd_917656 : Nat := 4983230072969 + 3 ^ 40 * 917656 * 2
def baseEnd_917656 : Nat := 15512711225756934991927

theorem tailTrace_917656 : CollatzResearch.WordTrace tailWord_917656 prefixEnd_917656 15512711225756934991927 := by
  unfold tailWord_917656
  simp only [CollatzResearch.WordTrace]
  refine ⟨16734831981748255006270411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22313109308997673341693881 16734831981748255006270411)
  ·
    refine ⟨25102247972622382509405617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16734831981748255006270411 25102247972622382509405617)
    ·
      refine ⟨18826685979466786882054213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25102247972622382509405617 18826685979466786882054213)
      ·
        refine ⟨3530003621150022540385165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18826685979466786882054213 3530003621150022540385165)
        ·
          refine ⟨1323751357931258452644437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3530003621150022540385165 1323751357931258452644437)
          ·
            refine ⟨15512711225756934991927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1323751357931258452644437 15512711225756934991927)
            ·
              rfl

theorem cell20_917656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 8].length) (baseStart_917656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917656 prefixEnd_917656 := by exact prefixLift 917656
  have htrace : WordTrace (prefixWord ++ tailWord_917656) baseStart_917656 baseEnd_917656 := by
    simpa [prefixWord, tailWord_917656, baseEnd_917656] using wordTrace_append hprefix tailTrace_917656
  have hstable : (prefixWord ++ tailWord_917656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917656).length < 2 ^ (prefixWord ++ tailWord_917656).sum := by decide
  have hdescent : baseEnd_917656 < baseStart_917656 := by decide
  rcases family_descends (prefixWord ++ tailWord_917656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917662 : List Nat := [4, 3, 1, 1, 3, 1, 1, 4, 2]
def baseStart_917662 : Nat := 118140960795 + 917662 * 2 ^ 59
def prefixEnd_917662 : Nat := 4983230072969 + 3 ^ 40 * 917662 * 2
def baseEnd_917662 : Nat := 418845941658927890582005

theorem tailTrace_917662 : CollatzResearch.WordTrace tailWord_917662 prefixEnd_917662 418845941658927890582005 := by
  unfold tailWord_917662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4183735350184346629657405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22313255200983182024839493 4183735350184346629657405)
  ·
    refine ⟨1568900756319129986121527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4183735350184346629657405 1568900756319129986121527)
    ·
      refine ⟨2353351134478694979182291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1568900756319129986121527 2353351134478694979182291)
      ·
        refine ⟨3530026701718042468773437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2353351134478694979182291 3530026701718042468773437)
        ·
          refine ⟨1323760013144265925790039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3530026701718042468773437 1323760013144265925790039)
          ·
            refine ⟨1985640019716398888685059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323760013144265925790039 1985640019716398888685059)
            ·
              refine ⟨2978460029574598333027589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1985640019716398888685059 2978460029574598333027589)
              ·
                refine ⟨558461255545237187442673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2978460029574598333027589 558461255545237187442673)
                ·
                  refine ⟨418845941658927890582005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558461255545237187442673 418845941658927890582005)
                  ·
                    rfl

theorem cell20_917662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_917662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917662 prefixEnd_917662 := by exact prefixLift 917662
  have htrace : WordTrace (prefixWord ++ tailWord_917662) baseStart_917662 baseEnd_917662 := by
    simpa [prefixWord, tailWord_917662, baseEnd_917662] using wordTrace_append hprefix tailTrace_917662
  have hstable : (prefixWord ++ tailWord_917662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917662).length < 2 ^ (prefixWord ++ tailWord_917662).sum := by decide
  have hdescent : baseEnd_917662 < baseStart_917662 := by decide
  rcases family_descends (prefixWord ++ tailWord_917662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917687 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 4]
def baseStart_917687 : Nat := 118140960795 + 917687 * 2 ^ 59
def prefixEnd_917687 : Nat := 4983230072969 + 3 ^ 40 * 917687 * 2
def baseEnd_917687 : Nat := 418857352340138914748569

theorem tailTrace_917687 : CollatzResearch.WordTrace tailWord_917687 prefixEnd_917687 418857352340138914748569 := by
  unfold tailWord_917687
  simp only [CollatzResearch.WordTrace]
  refine ⟨33470794626384202306919315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22313863084256134871279543 33470794626384202306919315)
  ·
    refine ⟨50206191939576303460378973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33470794626384202306919315 50206191939576303460378973)
    ·
      refine ⟨18827321977341113797642115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50206191939576303460378973 18827321977341113797642115)
      ·
        refine ⟨28240982966011670696463173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18827321977341113797642115 28240982966011670696463173)
        ·
          refine ⟨5295184306127188255586845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28240982966011670696463173 5295184306127188255586845)
          ·
            refine ⟨1985694114797695595845067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5295184306127188255586845 1985694114797695595845067)
            ·
              refine ⟨2978541172196543393767601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1985694114797695595845067 2978541172196543393767601)
              ·
                refine ⟨2233905879147407545325701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2978541172196543393767601 2233905879147407545325701)
                ·
                  refine ⟨418857352340138914748569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2233905879147407545325701 418857352340138914748569)
                  ·
                    rfl

theorem cell20_917687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 4].length) (baseStart_917687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917687 prefixEnd_917687 := by exact prefixLift 917687
  have htrace : WordTrace (prefixWord ++ tailWord_917687) baseStart_917687 baseEnd_917687 := by
    simpa [prefixWord, tailWord_917687, baseEnd_917687] using wordTrace_append hprefix tailTrace_917687
  have hstable : (prefixWord ++ tailWord_917687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917687).length < 2 ^ (prefixWord ++ tailWord_917687).sum := by decide
  have hdescent : baseEnd_917687 < baseStart_917687 := by decide
  rcases family_descends (prefixWord ++ tailWord_917687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917777 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 5]
def baseStart_917777 : Nat := 118140960795 + 917777 * 2 ^ 59
def prefixEnd_917777 : Nat := 4983230072969 + 3 ^ 40 * 917777 * 2
def baseEnd_917777 : Nat := 418898430792498601748201

theorem tailTrace_917777 : CollatzResearch.WordTrace tailWord_917777 prefixEnd_917777 418898430792498601748201 := by
  unfold tailWord_917777
  simp only [CollatzResearch.WordTrace]
  refine ⟨33474077196058147677695585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22316051464038765118463723 33474077196058147677695585)
  ·
    refine ⟨25105557897043610758271689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33474077196058147677695585 25105557897043610758271689)
    ·
      refine ⟨18829168422782708068703767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25105557897043610758271689 18829168422782708068703767)
      ·
        refine ⟨28243752634174062103055651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18829168422782708068703767 28243752634174062103055651)
        ·
          refine ⟨42365628951261093154583477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28243752634174062103055651 42365628951261093154583477)
          ·
            refine ⟨3971777714180727483242201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42365628951261093154583477 3971777714180727483242201)
            ·
              refine ⟨2978833285635545612431651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3971777714180727483242201 2978833285635545612431651)
              ·
                refine ⟨4468249928453318418647477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2978833285635545612431651 4468249928453318418647477)
                ·
                  refine ⟨418898430792498601748201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4468249928453318418647477 418898430792498601748201)
                  ·
                    rfl

theorem cell20_917777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_917777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917777 prefixEnd_917777 := by exact prefixLift 917777
  have htrace : WordTrace (prefixWord ++ tailWord_917777) baseStart_917777 baseEnd_917777 := by
    simpa [prefixWord, tailWord_917777, baseEnd_917777] using wordTrace_append hprefix tailTrace_917777
  have hstable : (prefixWord ++ tailWord_917777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917777).length < 2 ^ (prefixWord ++ tailWord_917777).sum := by decide
  have hdescent : baseEnd_917777 < baseStart_917777 := by decide
  rcases family_descends (prefixWord ++ tailWord_917777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917790 : List Nat := [4, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_917790 : Nat := 118140960795 + 917790 * 2 ^ 59
def prefixEnd_917790 : Nat := 4983230072969 + 3 ^ 40 * 917790 * 2
def baseEnd_917790 : Nat := 418904364346728334314815

theorem tailTrace_917790 : CollatzResearch.WordTrace tailWord_917790 prefixEnd_917790 418904364346728334314815 := by
  unfold tailWord_917790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4184318918126381362239853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22316367563340700598612549 4184318918126381362239853)
  ·
    refine ⟨1569119594297393010839945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4184318918126381362239853 1569119594297393010839945)
    ·
      refine ⟨1176839695723044758129959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1569119594297393010839945 1176839695723044758129959)
      ·
        refine ⟨1765259543584567137194939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176839695723044758129959 1765259543584567137194939)
        ·
          refine ⟨2647889315376850705792409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765259543584567137194939 2647889315376850705792409)
          ·
            refine ⟨1985916986532638029344307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2647889315376850705792409 1985916986532638029344307)
            ·
              refine ⟨2978875479798957044016461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1985916986532638029344307 2978875479798957044016461)
              ·
                refine ⟨1117078304924608891506173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2978875479798957044016461 1117078304924608891506173)
                ·
                  refine ⟨418904364346728334314815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1117078304924608891506173 418904364346728334314815)
                  ·
                    rfl

theorem cell20_917790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_917790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917790 prefixEnd_917790 := by exact prefixLift 917790
  have htrace : WordTrace (prefixWord ++ tailWord_917790) baseStart_917790 baseEnd_917790 := by
    simpa [prefixWord, tailWord_917790, baseEnd_917790] using wordTrace_append hprefix tailTrace_917790
  have hstable : (prefixWord ++ tailWord_917790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917790).length < 2 ^ (prefixWord ++ tailWord_917790).sum := by decide
  have hdescent : baseEnd_917790 < baseStart_917790 := by decide
  rcases family_descends (prefixWord ++ tailWord_917790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917825 : List Nat := [1, 2, 5, 2, 3, 7]
def baseStart_917825 : Nat := 118140960795 + 917825 * 2 ^ 59
def prefixEnd_917825 : Nat := 4983230072969 + 3 ^ 40 * 917825 * 2
def baseEnd_917825 : Nat := 15515568122237917338815

theorem tailTrace_917825 : CollatzResearch.WordTrace tailWord_917825 prefixEnd_917825 15515568122237917338815 := by
  unfold tailWord_917825
  simp only [CollatzResearch.WordTrace]
  refine ⟨33475827899884251875442929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22317218599922834583628619 33475827899884251875442929)
  ·
    refine ⟨25106870924913188906582197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33475827899884251875442929 25106870924913188906582197)
    ·
      refine ⟨2353769149210611459992081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25106870924913188906582197 2353769149210611459992081)
      ·
        refine ⟨1765326861907958594994061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2353769149210611459992081 1765326861907958594994061)
        ·
          refine ⟨661997573215484473122773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1765326861907958594994061 661997573215484473122773)
          ·
            refine ⟨15515568122237917338815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 661997573215484473122773 15515568122237917338815)
            ·
              rfl

theorem cell20_917825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 7].length) (baseStart_917825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917825 prefixEnd_917825 := by exact prefixLift 917825
  have htrace : WordTrace (prefixWord ++ tailWord_917825) baseStart_917825 baseEnd_917825 := by
    simpa [prefixWord, tailWord_917825, baseEnd_917825] using wordTrace_append hprefix tailTrace_917825
  have hstable : (prefixWord ++ tailWord_917825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917825).length < 2 ^ (prefixWord ++ tailWord_917825).sum := by decide
  have hdescent : baseEnd_917825 < baseStart_917825 := by decide
  rcases family_descends (prefixWord ++ tailWord_917825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917828 : List Nat := [2, 3, 4, 1, 2, 1, 2, 2, 3]
def baseStart_917828 : Nat := 118140960795 + 917828 * 2 ^ 59
def prefixEnd_917828 : Nat := 4983230072969 + 3 ^ 40 * 917828 * 2
def baseEnd_917828 : Nat := 418921708582169091047993

theorem tailTrace_917828 : CollatzResearch.WordTrace tailWord_917828 prefixEnd_917828 418921708582169091047993 := by
  unfold tailWord_917828
  simp only [CollatzResearch.WordTrace]
  refine ⟨16737968659436691693901069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22317291545915588925201425 16737968659436691693901069)
  ·
    refine ⟨6276738247288759385212901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16737968659436691693901069 6276738247288759385212901)
    ·
      refine ⟨1176888421366642384727419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6276738247288759385212901 1176888421366642384727419)
      ·
        refine ⟨1765332632049963577091129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176888421366642384727419 1765332632049963577091129)
        ·
          refine ⟨1323999474037472682818347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1765332632049963577091129 1323999474037472682818347)
          ·
            refine ⟨1985999211056209024227521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323999474037472682818347 1985999211056209024227521)
            ·
              refine ⟨1489499408292156768170641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1985999211056209024227521 1489499408292156768170641)
              ·
                refine ⟨1117124556219117576127981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1489499408292156768170641 1117124556219117576127981)
                ·
                  refine ⟨418921708582169091047993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1117124556219117576127981 418921708582169091047993)
                  ·
                    rfl

theorem cell20_917828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_917828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917828 prefixEnd_917828 := by exact prefixLift 917828
  have htrace : WordTrace (prefixWord ++ tailWord_917828) baseStart_917828 baseEnd_917828 := by
    simpa [prefixWord, tailWord_917828, baseEnd_917828] using wordTrace_append hprefix tailTrace_917828
  have hstable : (prefixWord ++ tailWord_917828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917828).length < 2 ^ (prefixWord ++ tailWord_917828).sum := by decide
  have hdescent : baseEnd_917828 < baseStart_917828 := by decide
  rcases family_descends (prefixWord ++ tailWord_917828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917863 : List Nat := [1, 1, 5, 1, 3, 2, 3, 4]
def baseStart_917863 : Nat := 118140960795 + 917863 * 2 ^ 59
def prefixEnd_917863 : Nat := 4983230072969 + 3 ^ 40 * 917863 * 2
def baseEnd_917863 : Nat := 139645894511954841627061

theorem tailTrace_917863 : CollatzResearch.WordTrace tailWord_917863 prefixEnd_917863 139645894511954841627061 := by
  unfold tailWord_917863
  simp only [CollatzResearch.WordTrace]
  refine ⟨33477213873746584365326243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22318142582497722910217495 33477213873746584365326243)
  ·
    refine ⟨50215820810619876547989365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33477213873746584365326243 50215820810619876547989365)
    ·
      refine ⟨4707733200995613426374003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50215820810619876547989365 4707733200995613426374003)
      ·
        refine ⟨7061599801493420139561005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4707733200995613426374003 7061599801493420139561005)
        ·
          refine ⟨2648099925560032552335377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7061599801493420139561005 2648099925560032552335377)
          ·
            refine ⟨1986074944170024414251533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2648099925560032552335377 1986074944170024414251533)
            ·
              refine ⟨744778104063759155344325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1986074944170024414251533 744778104063759155344325)
              ·
                refine ⟨139645894511954841627061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 744778104063759155344325 139645894511954841627061)
                ·
                  rfl

theorem cell20_917863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 4].length) (baseStart_917863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917863 prefixEnd_917863 := by exact prefixLift 917863
  have htrace : WordTrace (prefixWord ++ tailWord_917863) baseStart_917863 baseEnd_917863 := by
    simpa [prefixWord, tailWord_917863, baseEnd_917863] using wordTrace_append hprefix tailTrace_917863
  have hstable : (prefixWord ++ tailWord_917863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917863).length < 2 ^ (prefixWord ++ tailWord_917863).sum := by decide
  have hdescent : baseEnd_917863 < baseStart_917863 := by decide
  rcases family_descends (prefixWord ++ tailWord_917863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917918 : List Nat := [4, 3, 1, 2, 1, 1, 4, 4]
def baseStart_917918 : Nat := 118140960795 + 917918 * 2 ^ 59
def prefixEnd_917918 : Nat := 4983230072969 + 3 ^ 40 * 917918 * 2
def baseEnd_917918 : Nat := 139654262344842926015875

theorem tailTrace_917918 : CollatzResearch.WordTrace tailWord_917918 prefixEnd_917918 139654262344842926015875 := by
  unfold tailWord_917918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4184902486068416094822301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22319479925698219172385605 4184902486068416094822301)
  ·
    refine ⟨1569338432275656035558363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4184902486068416094822301 1569338432275656035558363)
    ·
      refine ⟨2354007648413484053337545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1569338432275656035558363 2354007648413484053337545)
      ·
        refine ⟨1765505736310113040003159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2354007648413484053337545 1765505736310113040003159)
        ·
          refine ⟨2648258604465169560004739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765505736310113040003159 2648258604465169560004739)
          ·
            refine ⟨3972387906697754340007109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648258604465169560004739 3972387906697754340007109)
            ·
              refine ⟨744822732505828938751333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3972387906697754340007109 744822732505828938751333)
              ·
                refine ⟨139654262344842926015875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 744822732505828938751333 139654262344842926015875)
                ·
                  rfl

theorem cell20_917918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_917918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917918 prefixEnd_917918 := by exact prefixLift 917918
  have htrace : WordTrace (prefixWord ++ tailWord_917918) baseStart_917918 baseEnd_917918 := by
    simpa [prefixWord, tailWord_917918, baseEnd_917918] using wordTrace_append hprefix tailTrace_917918
  have hstable : (prefixWord ++ tailWord_917918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917918).length < 2 ^ (prefixWord ++ tailWord_917918).sum := by decide
  have hdescent : baseEnd_917918 < baseStart_917918 := by decide
  rcases family_descends (prefixWord ++ tailWord_917918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917922 : List Nat := [3, 3, 1, 2, 1, 1, 3, 6]
def baseStart_917922 : Nat := 118140960795 + 917922 * 2 ^ 59
def prefixEnd_917922 : Nat := 4983230072969 + 3 ^ 40 * 917922 * 2
def baseEnd_917922 : Nat := 139654870914507513971425

theorem tailTrace_917922 : CollatzResearch.WordTrace tailWord_917922 prefixEnd_917922 139654870914507513971425 := by
  unfold tailWord_917922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8369841445133209360431005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22319577187021891627816013 8369841445133209360431005)
  ·
    refine ⟨3138690541924953510161627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8369841445133209360431005 3138690541924953510161627)
    ·
      refine ⟨4708035812887430265242441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3138690541924953510161627 4708035812887430265242441)
      ·
        refine ⟨3531026859665572698931831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4708035812887430265242441 3531026859665572698931831)
        ·
          refine ⟨5296540289498359048397747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531026859665572698931831 5296540289498359048397747)
          ·
            refine ⟨7944810434247538572596621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5296540289498359048397747 7944810434247538572596621)
            ·
              refine ⟨2979303912842826964723733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7944810434247538572596621 2979303912842826964723733)
              ·
                refine ⟨139654870914507513971425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2979303912842826964723733 139654870914507513971425)
                ·
                  rfl

theorem cell20_917922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_917922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917922 prefixEnd_917922 := by exact prefixLift 917922
  have htrace : WordTrace (prefixWord ++ tailWord_917922) baseStart_917922 baseEnd_917922 := by
    simpa [prefixWord, tailWord_917922, baseEnd_917922] using wordTrace_append hprefix tailTrace_917922
  have hstable : (prefixWord ++ tailWord_917922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917922).length < 2 ^ (prefixWord ++ tailWord_917922).sum := by decide
  have hdescent : baseEnd_917922 < baseStart_917922 := by decide
  rcases family_descends (prefixWord ++ tailWord_917922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917928 : List Nat := [2, 1, 6, 1, 1, 3, 1, 3, 2]
def baseStart_917928 : Nat := 118140960795 + 917928 * 2 ^ 59
def prefixEnd_917928 : Nat := 4983230072969 + 3 ^ 40 * 917928 * 2
def baseEnd_917928 : Nat := 418967351307013187714251

theorem tailTrace_917928 : CollatzResearch.WordTrace tailWord_917928 prefixEnd_917928 418967351307013187714251 := by
  unfold tailWord_917928
  simp only [CollatzResearch.WordTrace]
  refine ⟨16739792309255550233221219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22319723079007400310961625 16739792309255550233221219)
  ·
    refine ⟨25109688463883325349831829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16739792309255550233221219 25109688463883325349831829)
    ·
      refine ⟨1177016646744530875773367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25109688463883325349831829 1177016646744530875773367)
      ·
        refine ⟨1765524970116796313660051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177016646744530875773367 1765524970116796313660051)
        ·
          refine ⟨2648287455175194470490077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765524970116796313660051 2648287455175194470490077)
          ·
            refine ⟨993107795690697926433779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2648287455175194470490077 993107795690697926433779)
            ·
              refine ⟨1489661693536046889650669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993107795690697926433779 1489661693536046889650669)
              ·
                refine ⟨558623135076017583619001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1489661693536046889650669 558623135076017583619001)
                ·
                  refine ⟨418967351307013187714251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558623135076017583619001 418967351307013187714251)
                  ·
                    rfl

theorem cell20_917928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 2].length) (baseStart_917928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917928 prefixEnd_917928 := by exact prefixLift 917928
  have htrace : WordTrace (prefixWord ++ tailWord_917928) baseStart_917928 baseEnd_917928 := by
    simpa [prefixWord, tailWord_917928, baseEnd_917928] using wordTrace_append hprefix tailTrace_917928
  have hstable : (prefixWord ++ tailWord_917928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917928).length < 2 ^ (prefixWord ++ tailWord_917928).sum := by decide
  have hdescent : baseEnd_917928 < baseStart_917928 := by decide
  rcases family_descends (prefixWord ++ tailWord_917928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917943 : List Nat := [1, 1, 3, 1, 3, 3, 8]
def baseStart_917943 : Nat := 118140960795 + 917943 * 2 ^ 59
def prefixEnd_917943 : Nat := 4983230072969 + 3 ^ 40 * 917943 * 2
def baseEnd_917943 : Nat := 46552688635082200246021

theorem tailTrace_917943 : CollatzResearch.WordTrace tailWord_917943 prefixEnd_917943 46552688635082200246021 := by
  unfold tailWord_917943
  simp only [CollatzResearch.WordTrace]
  refine ⟨33480131713456758028238483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22320087808971172018825655 33480131713456758028238483)
  ·
    refine ⟨50220197570185137042357725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33480131713456758028238483 50220197570185137042357725)
    ·
      refine ⟨18832574088819426390884147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50220197570185137042357725 18832574088819426390884147)
      ·
        refine ⟨28248861133229139586326221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18832574088819426390884147 28248861133229139586326221)
        ·
          refine ⟨10593322924960927344872333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28248861133229139586326221 10593322924960927344872333)
          ·
            refine ⟨3972496096860347754327125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10593322924960927344872333 3972496096860347754327125)
            ·
              refine ⟨46552688635082200246021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3972496096860347754327125 46552688635082200246021)
              ·
                rfl

theorem cell20_917943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 8].length) (baseStart_917943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917943 prefixEnd_917943 := by exact prefixLift 917943
  have htrace : WordTrace (prefixWord ++ tailWord_917943) baseStart_917943 baseEnd_917943 := by
    simpa [prefixWord, tailWord_917943, baseEnd_917943] using wordTrace_append hprefix tailTrace_917943
  have hstable : (prefixWord ++ tailWord_917943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917943).length < 2 ^ (prefixWord ++ tailWord_917943).sum := by decide
  have hdescent : baseEnd_917943 < baseStart_917943 := by decide
  rcases family_descends (prefixWord ++ tailWord_917943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917949 : List Nat := [1, 4, 1, 2, 2, 3, 3, 2, 2]
def baseStart_917949 : Nat := 118140960795 + 917949 * 2 ^ 59
def prefixEnd_917949 : Nat := 4983230072969 + 3 ^ 40 * 917949 * 2
def baseEnd_917949 : Nat := 418976936279230448014165

theorem tailTrace_917949 : CollatzResearch.WordTrace tailWord_917949 prefixEnd_917949 418976936279230448014165 := by
  unfold tailWord_917949
  simp only [CollatzResearch.WordTrace]
  refine ⟨33480350551435021052956901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22320233700956680701971267 33480350551435021052956901)
  ·
    refine ⟨6277565728394066447429419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33480350551435021052956901 6277565728394066447429419)
    ·
      refine ⟨9416348592591099671144129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6277565728394066447429419 9416348592591099671144129)
      ·
        refine ⟨7062261444443324753358097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9416348592591099671144129 7062261444443324753358097)
        ·
          refine ⟨5296696083332493565018573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7062261444443324753358097 5296696083332493565018573)
          ·
            refine ⟨1986261031249685086881965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5296696083332493565018573 1986261031249685086881965)
            ·
              refine ⟨744847886718631907580737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1986261031249685086881965 744847886718631907580737)
              ·
                refine ⟨558635915038973930685553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 744847886718631907580737 558635915038973930685553)
                ·
                  refine ⟨418976936279230448014165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558635915038973930685553 418976936279230448014165)
                  ·
                    rfl

theorem cell20_917949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_917949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917949 prefixEnd_917949 := by exact prefixLift 917949
  have htrace : WordTrace (prefixWord ++ tailWord_917949) baseStart_917949 baseEnd_917949 := by
    simpa [prefixWord, tailWord_917949, baseEnd_917949] using wordTrace_append hprefix tailTrace_917949
  have hstable : (prefixWord ++ tailWord_917949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917949).length < 2 ^ (prefixWord ++ tailWord_917949).sum := by decide
  have hdescent : baseEnd_917949 < baseStart_917949 := by decide
  rcases family_descends (prefixWord ++ tailWord_917949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917960 : List Nat := [2, 1, 3, 1, 3, 3, 2, 5]
def baseStart_917960 : Nat := 118140960795 + 917960 * 2 ^ 59
def prefixEnd_917960 : Nat := 4983230072969 + 3 ^ 40 * 917960 * 2
def baseEnd_917960 : Nat := 139660652326321099549151

theorem tailTrace_917960 : CollatzResearch.WordTrace tailWord_917960 prefixEnd_917960 139660652326321099549151 := by
  unfold tailWord_917960
  simp only [CollatzResearch.WordTrace]
  refine ⟨16740375877197584965803667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22320501169596779954404889 16740375877197584965803667)
  ·
    refine ⟨25110563815796377448705501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16740375877197584965803667 25110563815796377448705501)
    ·
      refine ⟨9416461430923641543264563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25110563815796377448705501 9416461430923641543264563)
      ·
        refine ⟨14124692146385462314896845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9416461430923641543264563 14124692146385462314896845)
        ·
          refine ⟨5296759554894548368086317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14124692146385462314896845 5296759554894548368086317)
          ·
            refine ⟨1986284833085455638032369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5296759554894548368086317 1986284833085455638032369)
            ·
              refine ⟨1489713624814091728524277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1986284833085455638032369 1489713624814091728524277)
              ·
                refine ⟨139660652326321099549151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1489713624814091728524277 139660652326321099549151)
                ·
                  rfl

theorem cell20_917960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_917960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_917960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_917960 prefixEnd_917960 := by exact prefixLift 917960
  have htrace : WordTrace (prefixWord ++ tailWord_917960) baseStart_917960 baseEnd_917960 := by
    simpa [prefixWord, tailWord_917960, baseEnd_917960] using wordTrace_append hprefix tailTrace_917960
  have hstable : (prefixWord ++ tailWord_917960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917960).length < 2 ^ (prefixWord ++ tailWord_917960).sum := by decide
  have hdescent : baseEnd_917960 < baseStart_917960 := by decide
  rcases family_descends (prefixWord ++ tailWord_917960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918012 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 4]
def baseStart_918012 : Nat := 118140960795 + 918012 * 2 ^ 59
def prefixEnd_918012 : Nat := 4983230072969 + 3 ^ 40 * 918012 * 2
def baseEnd_918012 : Nat := 419005691195882228913907

theorem tailTrace_918012 : CollatzResearch.WordTrace tailWord_918012 prefixEnd_918012 419005691195882228913907 := by
  unfold tailWord_918012
  simp only [CollatzResearch.WordTrace]
  refine ⟨16741324175103391406250145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22321765566804521875000193 16741324175103391406250145)
  ·
    refine ⟨12555993131327543554687609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16741324175103391406250145 12555993131327543554687609)
    ·
      refine ⟨9416994848495657666015707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12555993131327543554687609 9416994848495657666015707)
      ·
        refine ⟨14125492272743486499023561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9416994848495657666015707 14125492272743486499023561)
        ·
          refine ⟨10594119204557614874267671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14125492272743486499023561 10594119204557614874267671)
          ·
            refine ⟨15891178806836422311401507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10594119204557614874267671 15891178806836422311401507)
            ·
              refine ⟨23836768210254633467102261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15891178806836422311401507 23836768210254633467102261)
              ·
                refine ⟨2234697019711371887540837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23836768210254633467102261 2234697019711371887540837)
                ·
                  refine ⟨419005691195882228913907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2234697019711371887540837 419005691195882228913907)
                  ·
                    rfl

theorem cell20_918012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_918012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918012 prefixEnd_918012 := by exact prefixLift 918012
  have htrace : WordTrace (prefixWord ++ tailWord_918012) baseStart_918012 baseEnd_918012 := by
    simpa [prefixWord, tailWord_918012, baseEnd_918012] using wordTrace_append hprefix tailTrace_918012
  have hstable : (prefixWord ++ tailWord_918012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918012).length < 2 ^ (prefixWord ++ tailWord_918012).sum := by decide
  have hdescent : baseEnd_918012 < baseStart_918012 := by decide
  rcases family_descends (prefixWord ++ tailWord_918012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918050 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_918050 : Nat := 118140960795 + 918050 * 2 ^ 59
def prefixEnd_918050 : Nat := 4983230072969 + 3 ^ 40 * 918050 * 2
def baseEnd_918050 : Nat := 419023035431322985647085

theorem tailTrace_918050 : CollatzResearch.WordTrace tailWord_918050 prefixEnd_918050 419023035431322985647085 := by
  unfold tailWord_918050
  simp only [CollatzResearch.WordTrace]
  refine ⟨8371008581017278825595901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22322689549379410201589069 8371008581017278825595901)
  ·
    refine ⟨3139128217881479559598463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8371008581017278825595901 3139128217881479559598463)
    ·
      refine ⟨4708692326822219339397695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3139128217881479559598463 4708692326822219339397695)
      ·
        refine ⟨7063038490233329009096543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4708692326822219339397695 7063038490233329009096543)
        ·
          refine ⟨10594557735349993513644815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7063038490233329009096543 10594557735349993513644815)
          ·
            refine ⟨15891836603024990270467223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10594557735349993513644815 15891836603024990270467223)
            ·
              refine ⟨23837754904537485405700835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15891836603024990270467223 23837754904537485405700835)
              ·
                refine ⟨35756632356806228108551253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23837754904537485405700835 35756632356806228108551253)
                ·
                  refine ⟨419023035431322985647085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35756632356806228108551253 419023035431322985647085)
                  ·
                    rfl

theorem cell20_918050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_918050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918050 prefixEnd_918050 := by exact prefixLift 918050
  have htrace : WordTrace (prefixWord ++ tailWord_918050) baseStart_918050 baseEnd_918050 := by
    simpa [prefixWord, tailWord_918050, baseEnd_918050] using wordTrace_append hprefix tailTrace_918050
  have hstable : (prefixWord ++ tailWord_918050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918050).length < 2 ^ (prefixWord ++ tailWord_918050).sum := by decide
  have hdescent : baseEnd_918050 < baseStart_918050 := by decide
  rcases family_descends (prefixWord ++ tailWord_918050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918067 : List Nat := [1, 1, 1, 2, 4, 2, 1, 6, 2]
def baseStart_918067 : Nat := 118140960795 + 918067 * 2 ^ 59
def prefixEnd_918067 : Nat := 4983230072969 + 3 ^ 40 * 918067 * 2
def baseEnd_918067 : Nat := 419030794694546482080349

theorem tailTrace_918067 : CollatzResearch.WordTrace tailWord_918067 prefixEnd_918067 419030794694546482080349 := by
  unfold tailWord_918067
  simp only [CollatzResearch.WordTrace]
  refine ⟨33484654365007527205752455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22323102910005018137168303 33484654365007527205752455)
  ·
    refine ⟨50226981547511290808628683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33484654365007527205752455 50226981547511290808628683)
    ·
      refine ⟨75340472321266936212943025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50226981547511290808628683 75340472321266936212943025)
      ·
        refine ⟨56505354240950202159707269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75340472321266936212943025 56505354240950202159707269)
        ·
          refine ⟨10594753920178162904945113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56505354240950202159707269 10594753920178162904945113)
          ·
            refine ⟨7946065440133622178708835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10594753920178162904945113 7946065440133622178708835)
            ·
              refine ⟨11919098160200433268063253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7946065440133622178708835 11919098160200433268063253)
              ·
                refine ⟨558707726259395309440465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11919098160200433268063253 558707726259395309440465)
                ·
                  refine ⟨419030794694546482080349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558707726259395309440465 419030794694546482080349)
                  ·
                    rfl

theorem cell20_918067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 2].length) (baseStart_918067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918067 prefixEnd_918067 := by exact prefixLift 918067
  have htrace : WordTrace (prefixWord ++ tailWord_918067) baseStart_918067 baseEnd_918067 := by
    simpa [prefixWord, tailWord_918067, baseEnd_918067] using wordTrace_append hprefix tailTrace_918067
  have hstable : (prefixWord ++ tailWord_918067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918067).length < 2 ^ (prefixWord ++ tailWord_918067).sum := by decide
  have hdescent : baseEnd_918067 < baseStart_918067 := by decide
  rcases family_descends (prefixWord ++ tailWord_918067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918077 : List Nat := [1, 4, 1, 3, 2, 2, 3, 1, 3]
def baseStart_918077 : Nat := 118140960795 + 918077 * 2 ^ 59
def prefixEnd_918077 : Nat := 4983230072969 + 3 ^ 40 * 918077 * 2
def baseEnd_918077 : Nat := 419035358967030891746975

theorem tailTrace_918077 : CollatzResearch.WordTrace tailWord_918077 prefixEnd_918077 419035358967030891746975 := by
  unfold tailWord_918077
  simp only [CollatzResearch.WordTrace]
  refine ⟨33485019094971298913616485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22323346063314199275744323 33485019094971298913616485)
  ·
    refine ⟨6278441080307118546303091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33485019094971298913616485 6278441080307118546303091)
    ·
      refine ⟨9417661620460677819454637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6278441080307118546303091 9417661620460677819454637)
      ·
        refine ⟨3531623107672754182295489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9417661620460677819454637 3531623107672754182295489)
        ·
          refine ⟨2648717330754565636721617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3531623107672754182295489 2648717330754565636721617)
          ·
            refine ⟨1986537998065924227541213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2648717330754565636721617 1986537998065924227541213)
            ·
              refine ⟨744951749274721585327955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1986537998065924227541213 744951749274721585327955)
              ·
                refine ⟨1117427623912082377991933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744951749274721585327955 1117427623912082377991933)
                ·
                  refine ⟨419035358967030891746975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1117427623912082377991933 419035358967030891746975)
                  ·
                    rfl

theorem cell20_918077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_918077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918077 prefixEnd_918077 := by exact prefixLift 918077
  have htrace : WordTrace (prefixWord ++ tailWord_918077) baseStart_918077 baseEnd_918077 := by
    simpa [prefixWord, tailWord_918077, baseEnd_918077] using wordTrace_append hprefix tailTrace_918077
  have hstable : (prefixWord ++ tailWord_918077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918077).length < 2 ^ (prefixWord ++ tailWord_918077).sum := by decide
  have hdescent : baseEnd_918077 < baseStart_918077 := by decide
  rcases family_descends (prefixWord ++ tailWord_918077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918119 : List Nat := [1, 1, 5, 1, 1, 1, 1, 6, 3]
def baseStart_918119 : Nat := 118140960795 + 918119 * 2 ^ 59
def prefixEnd_918119 : Nat := 4983230072969 + 3 ^ 40 * 918119 * 2
def baseEnd_918119 : Nat := 419054528911465412346803

theorem tailTrace_918119 : CollatzResearch.WordTrace tailWord_918119 prefixEnd_918119 419054528911465412346803 := by
  unfold tailWord_918119
  simp only [CollatzResearch.WordTrace]
  refine ⟨33486550960819140086645411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22324367307212760057763607 33486550960819140086645411)
  ·
    refine ⟨50229826441228710129968117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33486550960819140086645411 50229826441228710129968117)
    ·
      refine ⟨4709046228865191574684511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50229826441228710129968117 4709046228865191574684511)
      ·
        refine ⟨7063569343297787362026767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4709046228865191574684511 7063569343297787362026767)
        ·
          refine ⟨10595354014946681043040151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7063569343297787362026767 10595354014946681043040151)
          ·
            refine ⟨15893031022420021564560227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10595354014946681043040151 15893031022420021564560227)
            ·
              refine ⟨23839546533630032346840341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15893031022420021564560227 23839546533630032346840341)
              ·
                refine ⟨1117478743763907766258141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23839546533630032346840341 1117478743763907766258141)
                ·
                  refine ⟨419054528911465412346803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1117478743763907766258141 419054528911465412346803)
                  ·
                    rfl

theorem cell20_918119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 3].length) (baseStart_918119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918119 prefixEnd_918119 := by exact prefixLift 918119
  have htrace : WordTrace (prefixWord ++ tailWord_918119) baseStart_918119 baseEnd_918119 := by
    simpa [prefixWord, tailWord_918119, baseEnd_918119] using wordTrace_append hprefix tailTrace_918119
  have hstable : (prefixWord ++ tailWord_918119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918119).length < 2 ^ (prefixWord ++ tailWord_918119).sum := by decide
  have hdescent : baseEnd_918119 < baseStart_918119 := by decide
  rcases family_descends (prefixWord ++ tailWord_918119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918195 : List Nat := [1, 1, 1, 2, 3, 4, 2, 3, 3]
def baseStart_918195 : Nat := 118140960795 + 918195 * 2 ^ 59
def prefixEnd_918195 : Nat := 4983230072969 + 3 ^ 40 * 918195 * 2
def baseEnd_918195 : Nat := 419089217382346925813159

theorem tailTrace_918195 : CollatzResearch.WordTrace tailWord_918195 prefixEnd_918195 419089217382346925813159 := by
  unfold tailWord_918195
  simp only [CollatzResearch.WordTrace]
  refine ⟨33489322908543805066412039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22326215272362536710941359 33489322908543805066412039)
  ·
    refine ⟨50233984362815707599618059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33489322908543805066412039 50233984362815707599618059)
    ·
      refine ⟨75350976544223561399427089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50233984362815707599618059 75350976544223561399427089)
      ·
        refine ⟨56513232408167671049570317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75350976544223561399427089 56513232408167671049570317)
        ·
          refine ⟨21192462153062876643588869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56513232408167671049570317 21192462153062876643588869)
          ·
            refine ⟨3973586653699289370672913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21192462153062876643588869 3973586653699289370672913)
            ·
              refine ⟨2980189990274467028004685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3973586653699289370672913 2980189990274467028004685)
              ·
                refine ⟨1117571246352925135501757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2980189990274467028004685 1117571246352925135501757)
                ·
                  refine ⟨419089217382346925813159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1117571246352925135501757 419089217382346925813159)
                  ·
                    rfl

theorem cell20_918195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 3].length) (baseStart_918195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918195 prefixEnd_918195 := by exact prefixLift 918195
  have htrace : WordTrace (prefixWord ++ tailWord_918195) baseStart_918195 baseEnd_918195 := by
    simpa [prefixWord, tailWord_918195, baseEnd_918195] using wordTrace_append hprefix tailTrace_918195
  have hstable : (prefixWord ++ tailWord_918195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918195).length < 2 ^ (prefixWord ++ tailWord_918195).sum := by decide
  have hdescent : baseEnd_918195 < baseStart_918195 := by decide
  rcases family_descends (prefixWord ++ tailWord_918195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918202 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_918202 : Nat := 118140960795 + 918202 * 2 ^ 59
def prefixEnd_918202 : Nat := 4983230072969 + 3 ^ 40 * 918202 * 2
def baseEnd_918202 : Nat := 419092412373086012579797

theorem tailTrace_918202 : CollatzResearch.WordTrace tailWord_918202 prefixEnd_918202 419092412373086012579797 := by
  unfold tailWord_918202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8372394554879611315479215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22326385479678963507944573 8372394554879611315479215)
  ·
    refine ⟨12558591832319416973218823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8372394554879611315479215 12558591832319416973218823)
    ·
      refine ⟨18837887748479125459828235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12558591832319416973218823 18837887748479125459828235)
      ·
        refine ⟨28256831622718688189742353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18837887748479125459828235 28256831622718688189742353)
        ·
          refine ⟨21192623717039016142306765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28256831622718688189742353 21192623717039016142306765)
          ·
            refine ⟨7947233893889631053365037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21192623717039016142306765 7947233893889631053365037)
            ·
              refine ⟨2980212710208611645011889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7947233893889631053365037 2980212710208611645011889)
              ·
                refine ⟨2235159532656458733758917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2980212710208611645011889 2235159532656458733758917)
                ·
                  refine ⟨419092412373086012579797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2235159532656458733758917 419092412373086012579797)
                  ·
                    rfl

theorem cell20_918202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_918202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918202 prefixEnd_918202 := by exact prefixLift 918202
  have htrace : WordTrace (prefixWord ++ tailWord_918202) baseStart_918202 baseEnd_918202 := by
    simpa [prefixWord, tailWord_918202, baseEnd_918202] using wordTrace_append hprefix tailTrace_918202
  have hstable : (prefixWord ++ tailWord_918202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918202).length < 2 ^ (prefixWord ++ tailWord_918202).sum := by decide
  have hdescent : baseEnd_918202 < baseStart_918202 := by decide
  rcases family_descends (prefixWord ++ tailWord_918202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918226 : List Nat := [3, 2, 2, 2, 3, 1, 7]
def baseStart_918226 : Nat := 118140960795 + 918226 * 2 ^ 59
def prefixEnd_918226 : Nat := 4983230072969 + 3 ^ 40 * 918226 * 2
def baseEnd_918226 : Nat := 46567040736338732864411

theorem tailTrace_918226 : CollatzResearch.WordTrace tailWord_918226 prefixEnd_918226 46567040736338732864411 := by
  unfold tailWord_918226
  simp only [CollatzResearch.WordTrace]
  refine ⟨8372613392857874340197633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22326969047620998240527021 8372613392857874340197633)
  ·
    refine ⟨6279460044643405755148225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8372613392857874340197633 6279460044643405755148225)
    ·
      refine ⟨4709595033482554316361169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6279460044643405755148225 4709595033482554316361169)
      ·
        refine ⟨3532196275111915737270877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4709595033482554316361169 3532196275111915737270877)
        ·
          refine ⟨1324573603166968401476579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3532196275111915737270877 1324573603166968401476579)
          ·
            refine ⟨1986860404750452602214869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324573603166968401476579 1986860404750452602214869)
            ·
              refine ⟨46567040736338732864411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1986860404750452602214869 46567040736338732864411)
              ·
                rfl

theorem cell20_918226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 7].length) (baseStart_918226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918226 prefixEnd_918226 := by exact prefixLift 918226
  have htrace : WordTrace (prefixWord ++ tailWord_918226) baseStart_918226 baseEnd_918226 := by
    simpa [prefixWord, tailWord_918226, baseEnd_918226] using wordTrace_append hprefix tailTrace_918226
  have hstable : (prefixWord ++ tailWord_918226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918226).length < 2 ^ (prefixWord ++ tailWord_918226).sum := by decide
  have hdescent : baseEnd_918226 < baseStart_918226 := by decide
  rcases family_descends (prefixWord ++ tailWord_918226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918236 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 4]
def baseStart_918236 : Nat := 118140960795 + 918236 * 2 ^ 59
def prefixEnd_918236 : Nat := 4983230072969 + 3 ^ 40 * 918236 * 2
def baseEnd_918236 : Nat := 419107930899533005446325

theorem tailTrace_918236 : CollatzResearch.WordTrace tailWord_918236 prefixEnd_918236 419107930899533005446325 := by
  unfold tailWord_918236
  simp only [CollatzResearch.WordTrace]
  refine ⟨16745409150697634534327281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22327212200930179379103041 16745409150697634534327281)
  ·
    refine ⟨12559056863023225900745461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16745409150697634534327281 12559056863023225900745461)
    ·
      refine ⟨1177411580908427428194887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12559056863023225900745461 1177411580908427428194887)
      ·
        refine ⟨1766117371362641142292331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177411580908427428194887 1766117371362641142292331)
        ·
          refine ⟨2649176057043961713438497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766117371362641142292331 2649176057043961713438497)
          ·
            refine ⟨1986882042782971285078873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2649176057043961713438497 1986882042782971285078873)
            ·
              refine ⟨1490161532087228463809155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1986882042782971285078873 1490161532087228463809155)
              ·
                refine ⟨2235242298130842695713733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1490161532087228463809155 2235242298130842695713733)
                ·
                  refine ⟨419107930899533005446325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2235242298130842695713733 419107930899533005446325)
                  ·
                    rfl

theorem cell20_918236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_918236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918236 prefixEnd_918236 := by exact prefixLift 918236
  have htrace : WordTrace (prefixWord ++ tailWord_918236) baseStart_918236 baseEnd_918236 := by
    simpa [prefixWord, tailWord_918236, baseEnd_918236] using wordTrace_append hprefix tailTrace_918236
  have hstable : (prefixWord ++ tailWord_918236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918236).length < 2 ^ (prefixWord ++ tailWord_918236).sum := by decide
  have hdescent : baseEnd_918236 < baseStart_918236 := by decide
  rcases family_descends (prefixWord ++ tailWord_918236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918260 : List Nat := [2, 6, 1, 1, 2, 1, 1, 6]
def baseStart_918260 : Nat := 118140960795 + 918260 * 2 ^ 59
def prefixEnd_918260 : Nat := 4983230072969 + 3 ^ 40 * 918260 * 2
def baseEnd_918260 : Nat := 139706295051165196215409

theorem tailTrace_918260 : CollatzResearch.WordTrace tailWord_918260 prefixEnd_918260 139706295051165196215409 := by
  unfold tailWord_918260
  simp only [CollatzResearch.WordTrace]
  refine ⟨16745846826654160583764117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22327795768872214111685489 16745846826654160583764117)
  ·
    refine ⟨784961569999413777363943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16745846826654160583764117 784961569999413777363943)
    ·
      refine ⟨1177442354999120666045915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 784961569999413777363943 1177442354999120666045915)
      ·
        refine ⟨1766163532498680999068873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177442354999120666045915 1766163532498680999068873)
        ·
          refine ⟨1324622649374010749301655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1766163532498680999068873 1324622649374010749301655)
          ·
            refine ⟨1986933974061016123952483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324622649374010749301655 1986933974061016123952483)
            ·
              refine ⟨2980400961091524185928725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1986933974061016123952483 2980400961091524185928725)
              ·
                refine ⟨139706295051165196215409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2980400961091524185928725 139706295051165196215409)
                ·
                  rfl

theorem cell20_918260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_918260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918260 prefixEnd_918260 := by exact prefixLift 918260
  have htrace : WordTrace (prefixWord ++ tailWord_918260) baseStart_918260 baseEnd_918260 := by
    simpa [prefixWord, tailWord_918260, baseEnd_918260] using wordTrace_append hprefix tailTrace_918260
  have hstable : (prefixWord ++ tailWord_918260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918260).length < 2 ^ (prefixWord ++ tailWord_918260).sum := by decide
  have hdescent : baseEnd_918260 < baseStart_918260 := by decide
  rcases family_descends (prefixWord ++ tailWord_918260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918301 : List Nat := [1, 4, 2, 4, 2, 1, 2, 1, 3]
def baseStart_918301 : Nat := 118140960795 + 918301 * 2 ^ 59
def prefixEnd_918301 : Nat := 4983230072969 + 3 ^ 40 * 918301 * 2
def baseEnd_918301 : Nat := 419137598670681668279393

theorem tailTrace_918301 : CollatzResearch.WordTrace tailWord_918301 prefixEnd_918301 419137598670681668279393 := by
  unfold tailWord_918301
  simp only [CollatzResearch.WordTrace]
  refine ⟨33493189046159785169770757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22328792697439856779847171 33493189046159785169770757)
  ·
    refine ⟨6279972946154959719332017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33493189046159785169770757 6279972946154959719332017)
    ·
      refine ⟨4709979709616219789499013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6279972946154959719332017 4709979709616219789499013)
      ·
        refine ⟨883121195553041210531065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4709979709616219789499013 883121195553041210531065)
        ·
          refine ⟨662340896664780907898299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 883121195553041210531065 662340896664780907898299)
          ·
            refine ⟨993511344997171361847449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662340896664780907898299 993511344997171361847449)
            ·
              refine ⟨745133508747878521385587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 993511344997171361847449 745133508747878521385587)
              ·
                refine ⟨1117700263121817782078381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745133508747878521385587 1117700263121817782078381)
                ·
                  refine ⟨419137598670681668279393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1117700263121817782078381 419137598670681668279393)
                  ·
                    rfl

theorem cell20_918301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_918301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918301 prefixEnd_918301 := by exact prefixLift 918301
  have htrace : WordTrace (prefixWord ++ tailWord_918301) baseStart_918301 baseEnd_918301 := by
    simpa [prefixWord, tailWord_918301, baseEnd_918301] using wordTrace_append hprefix tailTrace_918301
  have hstable : (prefixWord ++ tailWord_918301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918301).length < 2 ^ (prefixWord ++ tailWord_918301).sum := by decide
  have hdescent : baseEnd_918301 < baseStart_918301 := by decide
  rcases family_descends (prefixWord ++ tailWord_918301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918309 : List Nat := [1, 3, 1, 2, 3, 1, 3, 3, 3]
def baseStart_918309 : Nat := 118140960795 + 918309 * 2 ^ 59
def prefixEnd_918309 : Nat := 4983230072969 + 3 ^ 40 * 918309 * 2
def baseEnd_918309 : Nat := 419141250088669196012693

theorem tailTrace_918309 : CollatzResearch.WordTrace tailWord_918309 prefixEnd_918309 419141250088669196012693 := by
  unfold tailWord_918309
  simp only [CollatzResearch.WordTrace]
  refine ⟨33493480830130802536061981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22328987220087201690707987 33493480830130802536061981)
  ·
    refine ⟨12560055311299050951023243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33493480830130802536061981 12560055311299050951023243)
    ·
      refine ⟨18840082966948576426534865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12560055311299050951023243 18840082966948576426534865)
      ·
        refine ⟨14130062225211432319901149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18840082966948576426534865 14130062225211432319901149)
        ·
          refine ⟨5298773334454287119962931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14130062225211432319901149 5298773334454287119962931)
          ·
            refine ⟨7948160001681430679944397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5298773334454287119962931 7948160001681430679944397)
            ·
              refine ⟨2980560000630536504979149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7948160001681430679944397 2980560000630536504979149)
              ·
                refine ⟨1117710000236451189367181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2980560000630536504979149 1117710000236451189367181)
                ·
                  refine ⟨419141250088669196012693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1117710000236451189367181 419141250088669196012693)
                  ·
                    rfl

theorem cell20_918309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_918309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918309 prefixEnd_918309 := by exact prefixLift 918309
  have htrace : WordTrace (prefixWord ++ tailWord_918309) baseStart_918309 baseEnd_918309 := by
    simpa [prefixWord, tailWord_918309, baseEnd_918309] using wordTrace_append hprefix tailTrace_918309
  have hstable : (prefixWord ++ tailWord_918309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918309).length < 2 ^ (prefixWord ++ tailWord_918309).sum := by decide
  have hdescent : baseEnd_918309 < baseStart_918309 := by decide
  rcases family_descends (prefixWord ++ tailWord_918309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918323 : List Nat := [1, 1, 1, 2, 6, 1, 2, 6]
def baseStart_918323 : Nat := 118140960795 + 918323 * 2 ^ 59
def prefixEnd_918323 : Nat := 4983230072969 + 3 ^ 40 * 918323 * 2
def baseEnd_918323 : Nat := 139715880023382456515323

theorem tailTrace_918323 : CollatzResearch.WordTrace tailWord_918323 prefixEnd_918323 139715880023382456515323 := by
  unfold tailWord_918323
  simp only [CollatzResearch.WordTrace]
  refine ⟨33493991452080082927071623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22329327634720055284714415 33493991452080082927071623)
  ·
    refine ⟨50240987178120124390607435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33493991452080082927071623 50240987178120124390607435)
    ·
      refine ⟨75361480767180186585911153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50240987178120124390607435 75361480767180186585911153)
      ·
        refine ⟨56521110575385139939433365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75361480767180186585911153 56521110575385139939433365)
        ·
          refine ⟨2649427058221178434660939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56521110575385139939433365 2649427058221178434660939)
          ·
            refine ⟨3974140587331767651991409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2649427058221178434660939 3974140587331767651991409)
            ·
              refine ⟨2980605440498825738993557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3974140587331767651991409 2980605440498825738993557)
              ·
                refine ⟨139715880023382456515323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2980605440498825738993557 139715880023382456515323)
                ·
                  rfl

theorem cell20_918323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 6].length) (baseStart_918323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918323 prefixEnd_918323 := by exact prefixLift 918323
  have htrace : WordTrace (prefixWord ++ tailWord_918323) baseStart_918323 baseEnd_918323 := by
    simpa [prefixWord, tailWord_918323, baseEnd_918323] using wordTrace_append hprefix tailTrace_918323
  have hstable : (prefixWord ++ tailWord_918323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918323).length < 2 ^ (prefixWord ++ tailWord_918323).sum := by decide
  have hdescent : baseEnd_918323 < baseStart_918323 := by decide
  rcases family_descends (prefixWord ++ tailWord_918323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918340 : List Nat := [2, 3, 4, 2, 9]
def baseStart_918340 : Nat := 118140960795 + 918340 * 2 ^ 59
def prefixEnd_918340 : Nat := 4983230072969 + 3 ^ 40 * 918340 * 2
def baseEnd_918340 : Nat := 5174758016461368715793

theorem tailTrace_918340 : CollatzResearch.WordTrace tailWord_918340 prefixEnd_918340 5174758016461368715793 := by
  unfold tailWord_918340
  simp only [CollatzResearch.WordTrace]
  refine ⟨16747305746509247415220237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22329740995345663220293649 16747305746509247415220237)
  ·
    refine ⟨6280239654940967780707589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16747305746509247415220237 6280239654940967780707589)
    ·
      refine ⟨1177544935301431458882673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6280239654940967780707589 1177544935301431458882673)
      ·
        refine ⟨883158701476073594162005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1177544935301431458882673 883158701476073594162005)
        ·
          refine ⟨5174758016461368715793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 883158701476073594162005 5174758016461368715793)
          ·
            rfl

theorem cell20_918340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 9].length) (baseStart_918340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918340 prefixEnd_918340 := by exact prefixLift 918340
  have htrace : WordTrace (prefixWord ++ tailWord_918340) baseStart_918340 baseEnd_918340 := by
    simpa [prefixWord, tailWord_918340, baseEnd_918340] using wordTrace_append hprefix tailTrace_918340
  have hstable : (prefixWord ++ tailWord_918340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918340).length < 2 ^ (prefixWord ++ tailWord_918340).sum := by decide
  have hdescent : baseEnd_918340 < baseStart_918340 := by decide
  rcases family_descends (prefixWord ++ tailWord_918340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918342 : List Nat := [6, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_918342 : Nat := 118140960795 + 918342 * 2 ^ 59
def prefixEnd_918342 : Nat := 4983230072969 + 3 ^ 40 * 918342 * 2
def baseEnd_918342 : Nat := 419156312187867747912559

theorem tailTrace_918342 : CollatzResearch.WordTrace tailWord_918342 prefixEnd_918342 419156312187867747912559 := by
  unfold tailWord_918342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1046708888719101536625415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22329789626007499448008853 1046708888719101536625415)
  ·
    refine ⟨1570063333078652304938123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1046708888719101536625415 1570063333078652304938123)
    ·
      refine ⟨2355094999617978457407185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1570063333078652304938123 2355094999617978457407185)
      ·
        refine ⟨1766321249713483843055389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2355094999617978457407185 1766321249713483843055389)
        ·
          refine ⟨662370468642556441145771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1766321249713483843055389 662370468642556441145771)
          ·
            refine ⟨993555702963834661718657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662370468642556441145771 993555702963834661718657)
            ·
              refine ⟨745166777222875996288993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 993555702963834661718657 745166777222875996288993)
              ·
                refine ⟨558875082917156997216745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 745166777222875996288993 558875082917156997216745)
                ·
                  refine ⟨419156312187867747912559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558875082917156997216745 419156312187867747912559)
                  ·
                    rfl

theorem cell20_918342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_918342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_918342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_918342 prefixEnd_918342 := by exact prefixLift 918342
  have htrace : WordTrace (prefixWord ++ tailWord_918342) baseStart_918342 baseEnd_918342 := by
    simpa [prefixWord, tailWord_918342, baseEnd_918342] using wordTrace_append hprefix tailTrace_918342
  have hstable : (prefixWord ++ tailWord_918342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918342).length < 2 ^ (prefixWord ++ tailWord_918342).sum := by decide
  have hdescent : baseEnd_918342 < baseStart_918342 := by decide
  rcases family_descends (prefixWord ++ tailWord_918342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
