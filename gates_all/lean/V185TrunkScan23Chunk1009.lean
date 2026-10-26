import V185TrunkScan23Chunk1008

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5974265 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 1, 3, 6]
def baseStart_5974265 : Nat := 118140960795 + 5974265 * 2 ^ 59
def prefixEnd_5974265 : Nat := 4983230072969 + 3 ^ 40 * 5974265 * 2
def baseEnd_5974265 : Nat := 3067669502333173394412361

theorem tailTrace_5974265 : CollatzResearch.WordTrace tailWord_5974265 prefixEnd_5974265 3067669502333173394412361 := by
  unfold tailWord_5974265
  simp only [CollatzResearch.WordTrace]
  refine ⟨217899345701265703075028249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145266230467510468716685499 217899345701265703075028249)
  ·
    refine ⟨163424509275949277306271187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217899345701265703075028249 163424509275949277306271187)
    ·
      refine ⟨245136763913923915959406781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163424509275949277306271187 245136763913923915959406781)
      ·
        refine ⟨91926286467721468484777543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245136763913923915959406781 91926286467721468484777543)
        ·
          refine ⟨137889429701582202727166315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91926286467721468484777543 137889429701582202727166315)
          ·
            refine ⟨206834144552373304090749473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137889429701582202727166315 206834144552373304090749473)
            ·
              refine ⟨155125608414279978068062105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206834144552373304090749473 155125608414279978068062105)
              ·
                refine ⟨116344206310709983551046579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155125608414279978068062105 116344206310709983551046579)
                ·
                  refine ⟨174516309466064975326569869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116344206310709983551046579 174516309466064975326569869)
                  ·
                    refine ⟨65443616049774365747463701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 174516309466064975326569869 65443616049774365747463701)
                    ·
                      refine ⟨3067669502333173394412361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65443616049774365747463701 3067669502333173394412361)
                      ·
                        rfl

theorem cell23_5974265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_5974265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974265 prefixEnd_5974265 := by exact prefixLift 5974265
  have htrace : WordTrace (prefixWord ++ tailWord_5974265) baseStart_5974265 baseEnd_5974265 := by
    simpa [prefixWord, tailWord_5974265, baseEnd_5974265] using wordTrace_append hprefix tailTrace_5974265
  have hstable : (prefixWord ++ tailWord_5974265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974265).length < 2 ^ (prefixWord ++ tailWord_5974265).sum := by decide
  have hdescent : baseEnd_5974265 < baseStart_5974265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974272 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 3]
def baseStart_5974272 : Nat := 118140960795 + 5974272 * 2 ^ 59
def prefixEnd_5974272 : Nat := 4983230072969 + 3 ^ 40 * 5974272 * 2
def baseEnd_5974272 : Nat := 3067673096697754867024829

theorem tailTrace_5974272 : CollatzResearch.WordTrace tailWord_5974272 prefixEnd_5974272 3067673096697754867024829 := by
  unfold tailWord_5974272
  simp only [CollatzResearch.WordTrace]
  refine ⟨108949800506120171635266535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145266400674826895513688713 108949800506120171635266535)
  ·
    refine ⟨163424700759180257452899803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108949800506120171635266535 163424700759180257452899803)
    ·
      refine ⟨245137051138770386179349705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163424700759180257452899803 245137051138770386179349705)
      ·
        refine ⟨183852788354077789634512279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245137051138770386179349705 183852788354077789634512279)
        ·
          refine ⟨275779182531116684451768419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183852788354077789634512279 275779182531116684451768419)
          ·
            refine ⟨413668773796675026677652629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275779182531116684451768419 413668773796675026677652629)
            ·
              refine ⟨19390723771719141875514967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 413668773796675026677652629 19390723771719141875514967)
              ·
                refine ⟨29086085657578712813272451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19390723771719141875514967 29086085657578712813272451)
                ·
                  refine ⟨43629128486368069219908677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29086085657578712813272451 43629128486368069219908677)
                  ·
                    refine ⟨8180461591194012978732877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43629128486368069219908677 8180461591194012978732877)
                    ·
                      refine ⟨3067673096697754867024829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8180461591194012978732877 3067673096697754867024829)
                      ·
                        rfl

theorem cell23_5974272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_5974272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974272 prefixEnd_5974272 := by exact prefixLift 5974272
  have htrace : WordTrace (prefixWord ++ tailWord_5974272) baseStart_5974272 baseEnd_5974272 := by
    simpa [prefixWord, tailWord_5974272, baseEnd_5974272] using wordTrace_append hprefix tailTrace_5974272
  have hstable : (prefixWord ++ tailWord_5974272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974272).length < 2 ^ (prefixWord ++ tailWord_5974272).sum := by decide
  have hdescent : baseEnd_5974272 < baseStart_5974272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974275 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 10]
def baseStart_5974275 : Nat := 118140960795 + 5974275 * 2 ^ 59
def prefixEnd_5974275 : Nat := 4983230072969 + 3 ^ 40 * 5974275 * 2
def baseEnd_5974275 : Nat := 340852737459968706143035

theorem tailTrace_5974275 : CollatzResearch.WordTrace tailWord_5974275 prefixEnd_5974275 340852737459968706143035 := by
  unfold tailWord_5974275
  simp only [CollatzResearch.WordTrace]
  refine ⟨217899710431229474782892279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145266473620819649855261519 217899710431229474782892279)
  ·
    refine ⟨326849565646844212174338419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217899710431229474782892279 326849565646844212174338419)
    ·
      refine ⟨490274348470266318261507629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326849565646844212174338419 490274348470266318261507629)
      ·
        refine ⟨183852880676349869348065361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 490274348470266318261507629 183852880676349869348065361)
        ·
          refine ⟨137889660507262402011049021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183852880676349869348065361 137889660507262402011049021)
          ·
            refine ⟨51708622690223400754143383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137889660507262402011049021 51708622690223400754143383)
            ·
              refine ⟨77562934035335101131215075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51708622690223400754143383 77562934035335101131215075)
              ·
                refine ⟨116344401053002651696822613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77562934035335101131215075 116344401053002651696822613)
                ·
                  refine ⟨340852737459968706143035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 116344401053002651696822613 340852737459968706143035)
                  ·
                    rfl

theorem cell23_5974275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 10].length) (baseStart_5974275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974275 prefixEnd_5974275 := by exact prefixLift 5974275
  have htrace : WordTrace (prefixWord ++ tailWord_5974275) baseStart_5974275 baseEnd_5974275 := by
    simpa [prefixWord, tailWord_5974275, baseEnd_5974275] using wordTrace_append hprefix tailTrace_5974275
  have hstable : (prefixWord ++ tailWord_5974275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974275).length < 2 ^ (prefixWord ++ tailWord_5974275).sum := by decide
  have hdescent : baseEnd_5974275 < baseStart_5974275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974289 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 3]
def baseStart_5974289 : Nat := 118140960795 + 5974289 * 2 ^ 59
def prefixEnd_5974289 : Nat := 4983230072969 + 3 ^ 40 * 5974289 * 2
def baseEnd_5974289 : Nat := 3067681825868881300512251

theorem tailTrace_5974289 : CollatzResearch.WordTrace tailWord_5974289 prefixEnd_5974289 3067681825868881300512251 := by
  unfold tailWord_5974289
  simp only [CollatzResearch.WordTrace]
  refine ⟨217900221053178755173901921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145266814035452503449267947 217900221053178755173901921)
  ·
    refine ⟨163425165789884066380426441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217900221053178755173901921 163425165789884066380426441)
    ·
      refine ⟨122568874342413049785319831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163425165789884066380426441 122568874342413049785319831)
      ·
        refine ⟨183853311513619574677979747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122568874342413049785319831 183853311513619574677979747)
        ·
          refine ⟨275779967270429362016969621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183853311513619574677979747 275779967270429362016969621)
          ·
            refine ⟨12927185965801376344545451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 275779967270429362016969621 12927185965801376344545451)
            ·
              refine ⟨19390778948702064516818177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12927185965801376344545451 19390778948702064516818177)
              ·
                refine ⟨14543084211526548387613633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19390778948702064516818177 14543084211526548387613633)
                ·
                  refine ⟨10907313158644911290710225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14543084211526548387613633 10907313158644911290710225)
                  ·
                    refine ⟨8180484868983683468032669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10907313158644911290710225 8180484868983683468032669)
                    ·
                      refine ⟨3067681825868881300512251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8180484868983683468032669 3067681825868881300512251)
                      ·
                        rfl

theorem cell23_5974289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_5974289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974289 prefixEnd_5974289 := by exact prefixLift 5974289
  have htrace : WordTrace (prefixWord ++ tailWord_5974289) baseStart_5974289 baseEnd_5974289 := by
    simpa [prefixWord, tailWord_5974289, baseEnd_5974289] using wordTrace_append hprefix tailTrace_5974289
  have hstable : (prefixWord ++ tailWord_5974289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974289).length < 2 ^ (prefixWord ++ tailWord_5974289).sum := by decide
  have hdescent : baseEnd_5974289 < baseStart_5974289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974309 : List Nat := [1, 3, 1, 2, 5, 1, 1, 3, 6]
def baseStart_5974309 : Nat := 118140960795 + 5974309 * 2 ^ 59
def prefixEnd_5974309 : Nat := 4983230072969 + 3 ^ 40 * 5974309 * 2
def baseEnd_5974309 : Nat := 340854677275774580251351

theorem tailTrace_5974309 : CollatzResearch.WordTrace tailWord_5974309 prefixEnd_5974309 340854677275774580251351 := by
  unfold tailWord_5974309
  simp only [CollatzResearch.WordTrace]
  refine ⟨217900950513106298589629981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145267300342070865726419987 217900950513106298589629981)
  ·
    refine ⟨81712856442414861971111243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217900950513106298589629981 81712856442414861971111243)
    ·
      refine ⟨122569284663622292956666865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81712856442414861971111243 122569284663622292956666865)
      ·
        refine ⟨91926963497716719717500149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122569284663622292956666865 91926963497716719717500149)
        ·
          refine ⟨8618152827910942473515639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91926963497716719717500149 8618152827910942473515639)
          ·
            refine ⟨12927229241866413710273459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8618152827910942473515639 12927229241866413710273459)
            ·
              refine ⟨19390843862799620565410189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12927229241866413710273459 19390843862799620565410189)
              ·
                refine ⟨7271566448549857712028821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19390843862799620565410189 7271566448549857712028821)
                ·
                  refine ⟨340854677275774580251351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7271566448549857712028821 340854677275774580251351)
                  ·
                    rfl

theorem cell23_5974309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 6].length) (baseStart_5974309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974309 prefixEnd_5974309 := by exact prefixLift 5974309
  have htrace : WordTrace (prefixWord ++ tailWord_5974309) baseStart_5974309 baseEnd_5974309 := by
    simpa [prefixWord, tailWord_5974309, baseEnd_5974309] using wordTrace_append hprefix tailTrace_5974309
  have hstable : (prefixWord ++ tailWord_5974309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974309).length < 2 ^ (prefixWord ++ tailWord_5974309).sum := by decide
  have hdescent : baseEnd_5974309 < baseStart_5974309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974319 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 3, 1, 3]
def baseStart_5974319 : Nat := 118140960795 + 5974319 * 2 ^ 59
def prefixEnd_5974319 : Nat := 4983230072969 + 3 ^ 40 * 5974319 * 2
def baseEnd_5974319 : Nat := 3067697230288516183137113

theorem tailTrace_5974319 : CollatzResearch.WordTrace tailWord_5974319 prefixEnd_5974319 3067697230288516183137113 := by
  unfold tailWord_5974319
  simp only [CollatzResearch.WordTrace]
  refine ⟨217901315243070070297494011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145267543495380046864996007 217901315243070070297494011)
  ·
    refine ⟨326851972864605105446241017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217901315243070070297494011 326851972864605105446241017)
    ·
      refine ⟨245138979648453829084680763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326851972864605105446241017 245138979648453829084680763)
      ·
        refine ⟨367708469472680743627021145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245138979648453829084680763 367708469472680743627021145)
        ·
          refine ⟨275781352104510557720265859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367708469472680743627021145 275781352104510557720265859)
          ·
            refine ⟨413672028156765836580398789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275781352104510557720265859 413672028156765836580398789)
            ·
              refine ⟨77563505279393594358824773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 413672028156765836580398789 77563505279393594358824773)
              ·
                refine ⟨14543157239886298942279645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77563505279393594358824773 14543157239886298942279645)
                ·
                  refine ⟨5453683964957362103354867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14543157239886298942279645 5453683964957362103354867)
                  ·
                    refine ⟨8180525947436043155032301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5453683964957362103354867 8180525947436043155032301)
                    ·
                      refine ⟨3067697230288516183137113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8180525947436043155032301 3067697230288516183137113)
                      ·
                        rfl

theorem cell23_5974319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 1, 3].length) (baseStart_5974319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974319 prefixEnd_5974319 := by exact prefixLift 5974319
  have htrace : WordTrace (prefixWord ++ tailWord_5974319) baseStart_5974319 baseEnd_5974319 := by
    simpa [prefixWord, tailWord_5974319, baseEnd_5974319] using wordTrace_append hprefix tailTrace_5974319
  have hstable : (prefixWord ++ tailWord_5974319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974319).length < 2 ^ (prefixWord ++ tailWord_5974319).sum := by decide
  have hdescent : baseEnd_5974319 < baseStart_5974319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974353 : List Nat := [1, 2, 2, 1, 4, 3, 1, 4, 1, 1, 3]
def baseStart_5974353 : Nat := 118140960795 + 5974353 * 2 ^ 59
def prefixEnd_5974353 : Nat := 4983230072969 + 3 ^ 40 * 5974353 * 2
def baseEnd_5974353 : Nat := 3067714688630769050111957

theorem tailTrace_5974353 : CollatzResearch.WordTrace tailWord_5974353 prefixEnd_5974353 3067714688630769050111957 := by
  unfold tailWord_5974353
  simp only [CollatzResearch.WordTrace]
  refine ⟨217902555324946894104231713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145268370216631262736154475 217902555324946894104231713)
  ·
    refine ⟨163426916493710170578173785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217902555324946894104231713 163426916493710170578173785)
    ·
      refine ⟨122570187370282627933630339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163426916493710170578173785 122570187370282627933630339)
      ·
        refine ⟨183855281055423941900445509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122570187370282627933630339 183855281055423941900445509)
        ·
          refine ⟨34472865197891989106333533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183855281055423941900445509 34472865197891989106333533)
          ·
            refine ⟨12927324449209495914875075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34472865197891989106333533 12927324449209495914875075)
            ·
              refine ⟨19390986673814243872312613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12927324449209495914875075 19390986673814243872312613)
              ·
                refine ⟨3635810001340170726058615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19390986673814243872312613 3635810001340170726058615)
                ·
                  refine ⟨5453715002010256089087923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3635810001340170726058615 5453715002010256089087923)
                  ·
                    refine ⟨8180572503015384133631885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5453715002010256089087923 8180572503015384133631885)
                    ·
                      refine ⟨3067714688630769050111957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8180572503015384133631885 3067714688630769050111957)
                      ·
                        rfl

theorem cell23_5974353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 1, 1, 3].length) (baseStart_5974353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974353 prefixEnd_5974353 := by exact prefixLift 5974353
  have htrace : WordTrace (prefixWord ++ tailWord_5974353) baseStart_5974353 baseEnd_5974353 := by
    simpa [prefixWord, tailWord_5974353, baseEnd_5974353] using wordTrace_append hprefix tailTrace_5974353
  have hstable : (prefixWord ++ tailWord_5974353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974353).length < 2 ^ (prefixWord ++ tailWord_5974353).sum := by decide
  have hdescent : baseEnd_5974353 < baseStart_5974353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974362 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5]
def baseStart_5974362 : Nat := 118140960795 + 5974362 * 2 ^ 59
def prefixEnd_5974362 : Nat := 4983230072969 + 3 ^ 40 * 5974362 * 2
def baseEnd_5974362 : Nat := 3067719309956659514899415

theorem tailTrace_5974362 : CollatzResearch.WordTrace tailWord_5974362 prefixEnd_5974362 3067719309956659514899415 := by
  unfold tailWord_5974362
  simp only [CollatzResearch.WordTrace]
  refine ⟨54475720895478572160327335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145268589054609525760872893 54475720895478572160327335)
  ·
    refine ⟨81713581343217858240491003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54475720895478572160327335 81713581343217858240491003)
    ·
      refine ⟨122570372014826787360736505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81713581343217858240491003 122570372014826787360736505)
      ·
        refine ⟨91927779011120090520552379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122570372014826787360736505 91927779011120090520552379)
        ·
          refine ⟨137891668516680135780828569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91927779011120090520552379 137891668516680135780828569)
          ·
            refine ⟨103418751387510101835621427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137891668516680135780828569 103418751387510101835621427)
            ·
              refine ⟨155128127081265152753432141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103418751387510101835621427 155128127081265152753432141)
              ·
                refine ⟨58173047655474432282537053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155128127081265152753432141 58173047655474432282537053)
                ·
                  refine ⟨21814892870802912105951395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58173047655474432282537053 21814892870802912105951395)
                  ·
                    refine ⟨32722339306204368158927093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21814892870802912105951395 32722339306204368158927093)
                    ·
                      refine ⟨3067719309956659514899415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32722339306204368158927093 3067719309956659514899415)
                      ·
                        rfl

theorem cell23_5974362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_5974362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974362 prefixEnd_5974362 := by exact prefixLift 5974362
  have htrace : WordTrace (prefixWord ++ tailWord_5974362) baseStart_5974362 baseEnd_5974362 := by
    simpa [prefixWord, tailWord_5974362, baseEnd_5974362] using wordTrace_append hprefix tailTrace_5974362
  have hstable : (prefixWord ++ tailWord_5974362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974362).length < 2 ^ (prefixWord ++ tailWord_5974362).sum := by decide
  have hdescent : baseEnd_5974362 < baseStart_5974362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974380 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 2, 3, 2]
def baseStart_5974380 : Nat := 118140960795 + 5974380 * 2 ^ 59
def prefixEnd_5974380 : Nat := 4983230072969 + 3 ^ 40 * 5974380 * 2
def baseEnd_5974380 : Nat := 3067728552608440444474333

theorem tailTrace_5974380 : CollatzResearch.WordTrace tailWord_5974380 prefixEnd_5974380 3067728552608440444474333 := by
  unfold tailWord_5974380
  simp only [CollatzResearch.WordTrace]
  refine ⟨108951770047924538857732297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145269026730566051810309729 108951770047924538857732297)
  ·
    refine ⟨81713827535943404143299223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108951770047924538857732297 81713827535943404143299223)
    ·
      refine ⟨122570741303915106214948835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81713827535943404143299223 122570741303915106214948835)
      ·
        refine ⟨183856111955872659322423253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122570741303915106214948835 183856111955872659322423253)
        ·
          refine ⟨4309127623965765452869295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 183856111955872659322423253 4309127623965765452869295)
          ·
            refine ⟨6463691435948648179303943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4309127623965765452869295 6463691435948648179303943)
            ·
              refine ⟨9695537153922972268955915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6463691435948648179303943 9695537153922972268955915)
              ·
                refine ⟨14543305730884458403433873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9695537153922972268955915 14543305730884458403433873)
                ·
                  refine ⟨10907479298163343802575405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14543305730884458403433873 10907479298163343802575405)
                  ·
                    refine ⟨4090304736811253925965777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10907479298163343802575405 4090304736811253925965777)
                    ·
                      refine ⟨3067728552608440444474333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4090304736811253925965777 3067728552608440444474333)
                      ·
                        rfl

theorem cell23_5974380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 2, 3, 2].length) (baseStart_5974380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974380 prefixEnd_5974380 := by exact prefixLift 5974380
  have htrace : WordTrace (prefixWord ++ tailWord_5974380) baseStart_5974380 baseEnd_5974380 := by
    simpa [prefixWord, tailWord_5974380, baseEnd_5974380] using wordTrace_append hprefix tailTrace_5974380
  have hstable : (prefixWord ++ tailWord_5974380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974380).length < 2 ^ (prefixWord ++ tailWord_5974380).sum := by decide
  have hdescent : baseEnd_5974380 < baseStart_5974380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974403 : List Nat := [1, 1, 1, 3, 6, 2, 1, 2, 2, 4]
def baseStart_5974403 : Nat := 118140960795 + 5974403 * 2 ^ 59
def prefixEnd_5974403 : Nat := 4983230072969 + 3 ^ 40 * 5974403 * 2
def baseEnd_5974403 : Nat := 1022580120887831284828909

theorem tailTrace_5974403 : CollatzResearch.WordTrace tailWord_5974403 prefixEnd_5974403 1022580120887831284828909 := by
  unfold tailWord_5974403
  simp only [CollatzResearch.WordTrace]
  refine ⟨217904378974765752643551863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145269585983177168429034575 217904378974765752643551863)
  ·
    refine ⟨326856568462148628965327795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217904378974765752643551863 326856568462148628965327795)
    ·
      refine ⟨490284852693222943447991693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326856568462148628965327795 490284852693222943447991693)
      ·
        refine ⟨183856819759958603792996885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 490284852693222943447991693 183856819759958603792996885)
        ·
          refine ⟨8618288426248059552796729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 183856819759958603792996885 8618288426248059552796729)
          ·
            refine ⟨6463716319686044664597547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8618288426248059552796729 6463716319686044664597547)
            ·
              refine ⟨9695574479529066996896321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6463716319686044664597547 9695574479529066996896321)
              ·
                refine ⟨7271680859646800247672241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9695574479529066996896321 7271680859646800247672241)
                ·
                  refine ⟨5453760644735100185754181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7271680859646800247672241 5453760644735100185754181)
                  ·
                    refine ⟨1022580120887831284828909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5453760644735100185754181 1022580120887831284828909)
                    ·
                      rfl

theorem cell23_5974403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 4].length) (baseStart_5974403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974403 prefixEnd_5974403 := by exact prefixLift 5974403
  have htrace : WordTrace (prefixWord ++ tailWord_5974403) baseStart_5974403 baseEnd_5974403 := by
    simpa [prefixWord, tailWord_5974403, baseEnd_5974403] using wordTrace_append hprefix tailTrace_5974403
  have hstable : (prefixWord ++ tailWord_5974403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974403).length < 2 ^ (prefixWord ++ tailWord_5974403).sum := by decide
  have hdescent : baseEnd_5974403 < baseStart_5974403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974420 : List Nat := [2, 4, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_5974420 : Nat := 118140960795 + 5974420 * 2 ^ 59
def prefixEnd_5974420 : Nat := 4983230072969 + 3 ^ 40 * 5974420 * 2
def baseEnd_5974420 : Nat := 1022583030611540095991383

theorem tailTrace_5974420 : CollatzResearch.WordTrace tailWord_5974420 prefixEnd_5974420 1022583030611540095991383 := by
  unfold tailWord_5974420
  simp only [CollatzResearch.WordTrace]
  refine ⟨108952499507852082273460357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145269999343802776364613809 108952499507852082273460357)
  ·
    refine ⟨20428593657722265426273817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108952499507852082273460357 20428593657722265426273817)
    ·
      refine ⟨15321445243291699069705363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20428593657722265426273817 15321445243291699069705363)
      ·
        refine ⟨22982167864937548604558045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15321445243291699069705363 22982167864937548604558045)
        ·
          refine ⟨8618312949351580726709267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22982167864937548604558045 8618312949351580726709267)
          ·
            refine ⟨12927469424027371090063901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8618312949351580726709267 12927469424027371090063901)
            ·
              refine ⟨4847801034010264158773963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12927469424027371090063901 4847801034010264158773963)
              ·
                refine ⟨7271701551015396238160945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4847801034010264158773963 7271701551015396238160945)
                ·
                  refine ⟨5453776163261547178620709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7271701551015396238160945 5453776163261547178620709)
                  ·
                    refine ⟨1022583030611540095991383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5453776163261547178620709 1022583030611540095991383)
                    ·
                      rfl

theorem cell23_5974420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_5974420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974420 prefixEnd_5974420 := by exact prefixLift 5974420
  have htrace : WordTrace (prefixWord ++ tailWord_5974420) baseStart_5974420 baseEnd_5974420 := by
    simpa [prefixWord, tailWord_5974420, baseEnd_5974420] using wordTrace_append hprefix tailTrace_5974420
  have hstable : (prefixWord ++ tailWord_5974420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974420).length < 2 ^ (prefixWord ++ tailWord_5974420).sum := by decide
  have hdescent : baseEnd_5974420 < baseStart_5974420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974426 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3]
def baseStart_5974426 : Nat := 118140960795 + 5974426 * 2 ^ 59
def prefixEnd_5974426 : Nat := 4983230072969 + 3 ^ 40 * 5974426 * 2
def baseEnd_5974426 : Nat := 3067752172718547264499121

theorem tailTrace_5974426 : CollatzResearch.WordTrace tailWord_5974426 prefixEnd_5974426 3067752172718547264499121 := by
  unfold tailWord_5974426
  simp only [CollatzResearch.WordTrace]
  refine ⟨54476304463420606892909783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145270145235788285047759421 54476304463420606892909783)
  ·
    refine ⟨81714456695130910339364675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54476304463420606892909783 81714456695130910339364675)
    ·
      refine ⟨122571685042696365509047013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81714456695130910339364675 122571685042696365509047013)
      ·
        refine ⟨22982190945505568532946315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122571685042696365509047013 22982190945505568532946315)
        ·
          refine ⟨34473286418258352799419473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22982190945505568532946315 34473286418258352799419473)
          ·
            refine ⟨25854964813693764599564605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34473286418258352799419473 25854964813693764599564605)
            ·
              refine ⟨9695611805135161724836727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25854964813693764599564605 9695611805135161724836727)
              ·
                refine ⟨14543417707702742587255091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9695611805135161724836727 14543417707702742587255091)
                ·
                  refine ⟨21815126561554113880882637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14543417707702742587255091 21815126561554113880882637)
                  ·
                    refine ⟨8180672460582792705330989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21815126561554113880882637 8180672460582792705330989)
                    ·
                      refine ⟨3067752172718547264499121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8180672460582792705330989 3067752172718547264499121)
                      ·
                        rfl

theorem cell23_5974426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_5974426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974426 prefixEnd_5974426 := by exact prefixLift 5974426
  have htrace : WordTrace (prefixWord ++ tailWord_5974426) baseStart_5974426 baseEnd_5974426 := by
    simpa [prefixWord, tailWord_5974426, baseEnd_5974426] using wordTrace_append hprefix tailTrace_5974426
  have hstable : (prefixWord ++ tailWord_5974426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974426).length < 2 ^ (prefixWord ++ tailWord_5974426).sum := by decide
  have hdescent : baseEnd_5974426 < baseStart_5974426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974430 : List Nat := [4, 3, 1, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_5974430 : Nat := 118140960795 + 5974430 * 2 ^ 59
def prefixEnd_5974430 : Nat := 4983230072969 + 3 ^ 40 * 5974430 * 2
def baseEnd_5974430 : Nat := 3067754226641165248849103

theorem tailTrace_5974430 : CollatzResearch.WordTrace tailWord_5974430 prefixEnd_5974430 3067754226641165248849103 := by
  unfold tailWord_5974430
  simp only [CollatzResearch.WordTrace]
  refine ⟨27238170468208492031848093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145270242497111957503189829 27238170468208492031848093)
  ·
    refine ⟨10214313925578184511943035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27238170468208492031848093 10214313925578184511943035)
    ·
      refine ⟨15321470888367276767914553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10214313925578184511943035 15321470888367276767914553)
      ·
        refine ⟨11491103166275457575935915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15321470888367276767914553 11491103166275457575935915)
        ·
          refine ⟨17236654749413186363903873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11491103166275457575935915 17236654749413186363903873)
          ·
            refine ⟨12927491062059889772927905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17236654749413186363903873 12927491062059889772927905)
            ·
              refine ⟨9695618296544917329695929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12927491062059889772927905 9695618296544917329695929)
              ·
                refine ⟨7271713722408687997271947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9695618296544917329695929 7271713722408687997271947)
                ·
                  refine ⟨10907570583613031995907921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7271713722408687997271947 10907570583613031995907921)
                  ·
                    refine ⟨8180677937709773996930941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10907570583613031995907921 8180677937709773996930941)
                    ·
                      refine ⟨3067754226641165248849103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8180677937709773996930941 3067754226641165248849103)
                      ·
                        rfl

theorem cell23_5974430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_5974430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974430 prefixEnd_5974430 := by exact prefixLift 5974430
  have htrace : WordTrace (prefixWord ++ tailWord_5974430) baseStart_5974430 baseEnd_5974430 := by
    simpa [prefixWord, tailWord_5974430, baseEnd_5974430] using wordTrace_append hprefix tailTrace_5974430
  have hstable : (prefixWord ++ tailWord_5974430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974430).length < 2 ^ (prefixWord ++ tailWord_5974430).sum := by decide
  have hdescent : baseEnd_5974430 < baseStart_5974430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974433 : List Nat := [1, 2, 3, 5, 1, 2, 2, 7]
def baseStart_5974433 : Nat := 118140960795 + 5974433 * 2 ^ 59
def prefixEnd_5974433 : Nat := 4983230072969 + 3 ^ 40 * 5974433 * 2
def baseEnd_5974433 : Nat := 113620583966041805078207

theorem tailTrace_5974433 : CollatzResearch.WordTrace tailWord_5974433 prefixEnd_5974433 113620583966041805078207 := by
  unfold tailWord_5974433
  simp only [CollatzResearch.WordTrace]
  refine ⟨217905473164657067767143953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145270315443104711844762635 217905473164657067767143953)
  ·
    refine ⟨163429104873492800825357965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217905473164657067767143953 163429104873492800825357965)
    ·
      refine ⟨61285914327559800309509237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163429104873492800825357965 61285914327559800309509237)
      ·
        refine ⟨5745554468208731279016491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61285914327559800309509237 5745554468208731279016491)
        ·
          refine ⟨8618331702313096918524737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5745554468208731279016491 8618331702313096918524737)
          ·
            refine ⟨6463748776734822688893553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8618331702313096918524737 6463748776734822688893553)
            ·
              refine ⟨4847811582551117016670165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6463748776734822688893553 4847811582551117016670165)
              ·
                refine ⟨113620583966041805078207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4847811582551117016670165 113620583966041805078207)
                ·
                  rfl

theorem cell23_5974433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 7].length) (baseStart_5974433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974433 prefixEnd_5974433 := by exact prefixLift 5974433
  have htrace : WordTrace (prefixWord ++ tailWord_5974433) baseStart_5974433 baseEnd_5974433 := by
    simpa [prefixWord, tailWord_5974433, baseEnd_5974433] using wordTrace_append hprefix tailTrace_5974433
  have hstable : (prefixWord ++ tailWord_5974433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974433).length < 2 ^ (prefixWord ++ tailWord_5974433).sum := by decide
  have hdescent : baseEnd_5974433 < baseStart_5974433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974436 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 3, 3, 2]
def baseStart_5974436 : Nat := 118140960795 + 5974436 * 2 ^ 59
def prefixEnd_5974436 : Nat := 4983230072969 + 3 ^ 40 * 5974436 * 2
def baseEnd_5974436 : Nat := 3067757307525092225374075

theorem tailTrace_5974436 : CollatzResearch.WordTrace tailWord_5974436 prefixEnd_5974436 3067757307525092225374075 := by
  unfold tailWord_5974436
  simp only [CollatzResearch.WordTrace]
  refine ⟨108952791291823099639751581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145270388389097466186335441 108952791291823099639751581)
  ·
    refine ⟨40857296734433662364906843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108952791291823099639751581 40857296734433662364906843)
    ·
      refine ⟨61285945101650493547360265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40857296734433662364906843 61285945101650493547360265)
      ·
        refine ⟨45964458826237870160520199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61285945101650493547360265 45964458826237870160520199)
        ·
          refine ⟨68946688239356805240780299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45964458826237870160520199 68946688239356805240780299)
          ·
            refine ⟨103420032359035207861170449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68946688239356805240780299 103420032359035207861170449)
            ·
              refine ⟨77565024269276405895877837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103420032359035207861170449 77565024269276405895877837)
              ·
                refine ⟨29086884100978652210954189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77565024269276405895877837 29086884100978652210954189)
                ·
                  refine ⟨10907581537866994579107821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29086884100978652210954189 10907581537866994579107821)
                  ·
                    refine ⟨4090343076700122967165433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10907581537866994579107821 4090343076700122967165433)
                    ·
                      refine ⟨3067757307525092225374075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4090343076700122967165433 3067757307525092225374075)
                      ·
                        rfl

theorem cell23_5974436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_5974436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974436 prefixEnd_5974436 := by exact prefixLift 5974436
  have htrace : WordTrace (prefixWord ++ tailWord_5974436) baseStart_5974436 baseEnd_5974436 := by
    simpa [prefixWord, tailWord_5974436, baseEnd_5974436] using wordTrace_append hprefix tailTrace_5974436
  have hstable : (prefixWord ++ tailWord_5974436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974436).length < 2 ^ (prefixWord ++ tailWord_5974436).sum := by decide
  have hdescent : baseEnd_5974436 < baseStart_5974436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974439 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_5974439 : Nat := 118140960795 + 5974439 * 2 ^ 59
def prefixEnd_5974439 : Nat := 4983230072969 + 3 ^ 40 * 5974439 * 2
def baseEnd_5974439 : Nat := 3067758847967055713636561

theorem tailTrace_5974439 : CollatzResearch.WordTrace tailWord_5974439 prefixEnd_5974439 3067758847967055713636561 := by
  unfold tailWord_5974439
  simp only [CollatzResearch.WordTrace]
  refine ⟨217905692002635330791862371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145270461335090220527908247 217905692002635330791862371)
  ·
    refine ⟨326858538003952996187793557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217905692002635330791862371 326858538003952996187793557)
    ·
      refine ⟨15321493968935296696302823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 326858538003952996187793557 15321493968935296696302823)
      ·
        refine ⟨22982240953402945044454235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15321493968935296696302823 22982240953402945044454235)
        ·
          refine ⟨34473361430104417566681353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22982240953402945044454235 34473361430104417566681353)
          ·
            refine ⟨25855021072578313175011015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34473361430104417566681353 25855021072578313175011015)
            ·
              refine ⟨38782531608867469762516523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25855021072578313175011015 38782531608867469762516523)
              ·
                refine ⟨58173797413301204643774785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38782531608867469762516523 58173797413301204643774785)
                ·
                  refine ⟨43630348059975903482831089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58173797413301204643774785 43630348059975903482831089)
                  ·
                    refine ⟨32722761044981927612123317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43630348059975903482831089 32722761044981927612123317)
                    ·
                      refine ⟨3067758847967055713636561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32722761044981927612123317 3067758847967055713636561)
                      ·
                        rfl

theorem cell23_5974439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_5974439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974439 prefixEnd_5974439 := by exact prefixLift 5974439
  have htrace : WordTrace (prefixWord ++ tailWord_5974439) baseStart_5974439 baseEnd_5974439 := by
    simpa [prefixWord, tailWord_5974439, baseEnd_5974439] using wordTrace_append hprefix tailTrace_5974439
  have hstable : (prefixWord ++ tailWord_5974439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974439).length < 2 ^ (prefixWord ++ tailWord_5974439).sum := by decide
  have hdescent : baseEnd_5974439 < baseStart_5974439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974486 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_5974486 : Nat := 118140960795 + 5974486 * 2 ^ 59
def prefixEnd_5974486 : Nat := 4983230072969 + 3 ^ 40 * 5974486 * 2
def baseEnd_5974486 : Nat := 3067782981557817029748845

theorem tailTrace_5974486 : CollatzResearch.WordTrace tailWord_5974486 prefixEnd_5974486 3067782981557817029748845 := by
  unfold tailWord_5974486
  simp only [CollatzResearch.WordTrace]
  refine ⟨13619212889591566113676457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145271604155643371879215541 13619212889591566113676457)
  ·
    refine ⟨10214409667193674585257343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13619212889591566113676457 10214409667193674585257343)
    ·
      refine ⟨15321614500790511877886015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10214409667193674585257343 15321614500790511877886015)
      ·
        refine ⟨22982421751185767816829023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15321614500790511877886015 22982421751185767816829023)
        ·
          refine ⟨34473632626778651725243535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22982421751185767816829023 34473632626778651725243535)
          ·
            refine ⟨51710448940167977587865303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34473632626778651725243535 51710448940167977587865303)
            ·
              refine ⟨77565673410251966381797955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51710448940167977587865303 77565673410251966381797955)
              ·
                refine ⟨116348510115377949572696933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77565673410251966381797955 116348510115377949572696933)
                ·
                  refine ⟨21815345646633365544880675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116348510115377949572696933 21815345646633365544880675)
                  ·
                    refine ⟨32723018469950048317321013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21815345646633365544880675 32723018469950048317321013)
                    ·
                      refine ⟨3067782981557817029748845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32723018469950048317321013 3067782981557817029748845)
                      ·
                        rfl

theorem cell23_5974486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_5974486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974486 prefixEnd_5974486 := by exact prefixLift 5974486
  have htrace : WordTrace (prefixWord ++ tailWord_5974486) baseStart_5974486 baseEnd_5974486 := by
    simpa [prefixWord, tailWord_5974486, baseEnd_5974486] using wordTrace_append hprefix tailTrace_5974486
  have hstable : (prefixWord ++ tailWord_5974486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974486).length < 2 ^ (prefixWord ++ tailWord_5974486).sum := by decide
  have hdescent : baseEnd_5974486 < baseStart_5974486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974534 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_5974534 : Nat := 118140960795 + 5974534 * 2 ^ 59
def prefixEnd_5974534 : Nat := 4983230072969 + 3 ^ 40 * 5974534 * 2
def baseEnd_5974534 : Nat := 3067807628629232841948625

theorem tailTrace_5974534 : CollatzResearch.WordTrace tailWord_5974534 prefixEnd_5974534 3067807628629232841948625 := by
  unfold tailWord_5974534
  simp only [CollatzResearch.WordTrace]
  refine ⟨6809661154290348813017833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145272771291527441344380437 6809661154290348813017833)
  ·
    refine ⟨5107245865717761609763375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6809661154290348813017833 5107245865717761609763375)
    ·
      refine ⟨7660868798576642414645063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5107245865717761609763375 7660868798576642414645063)
      ·
        refine ⟨11491303197864963621967595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7660868798576642414645063 11491303197864963621967595)
        ·
          refine ⟨17236954796797445432951393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11491303197864963621967595 17236954796797445432951393)
          ·
            refine ⟨12927716097598084074713545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17236954796797445432951393 12927716097598084074713545)
            ·
              refine ⟨9695787073198563056035159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12927716097598084074713545 9695787073198563056035159)
              ·
                refine ⟨14543680609797844584052739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9695787073198563056035159 14543680609797844584052739)
                ·
                  refine ⟨21815520914696766876079109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14543680609797844584052739 21815520914696766876079109)
                  ·
                    refine ⟨4090410171505643789264833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21815520914696766876079109 4090410171505643789264833)
                    ·
                      refine ⟨3067807628629232841948625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4090410171505643789264833 3067807628629232841948625)
                      ·
                        rfl

theorem cell23_5974534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_5974534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974534 prefixEnd_5974534 := by exact prefixLift 5974534
  have htrace : WordTrace (prefixWord ++ tailWord_5974534) baseStart_5974534 baseEnd_5974534 := by
    simpa [prefixWord, tailWord_5974534, baseEnd_5974534] using wordTrace_append hprefix tailTrace_5974534
  have hstable : (prefixWord ++ tailWord_5974534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974534).length < 2 ^ (prefixWord ++ tailWord_5974534).sum := by decide
  have hdescent : baseEnd_5974534 < baseStart_5974534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974556 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_5974556 : Nat := 118140960795 + 5974556 * 2 ^ 59
def prefixEnd_5974556 : Nat := 4983230072969 + 3 ^ 40 * 5974556 * 2
def baseEnd_5974556 : Nat := 3067818925203631755873523

theorem tailTrace_5974556 : CollatzResearch.WordTrace tailWord_5974556 prefixEnd_5974556 3067818925203631755873523 := by
  unfold tailWord_5974556
  simp only [CollatzResearch.WordTrace]
  refine ⟨108954979671605729886935761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145273306228807639849247681 108954979671605729886935761)
  ·
    refine ⟨81716234753704297415201821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108954979671605729886935761 81716234753704297415201821)
    ·
      refine ⟨30643588032639111530700683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81716234753704297415201821 30643588032639111530700683)
      ·
        refine ⟨45965382048958667296051025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30643588032639111530700683 45965382048958667296051025)
        ·
          refine ⟨34474036536719000472038269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45965382048958667296051025 34474036536719000472038269)
          ·
            refine ⟨12927763701269625177014351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34474036536719000472038269 12927763701269625177014351)
            ·
              refine ⟨19391645551904437765521527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12927763701269625177014351 19391645551904437765521527)
              ·
                refine ⟨29087468327856656648282291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19391645551904437765521527 29087468327856656648282291)
                ·
                  refine ⟨43631202491784984972423437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29087468327856656648282291 43631202491784984972423437)
                  ·
                    refine ⟨16361700934419369364658789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43631202491784984972423437 16361700934419369364658789)
                    ·
                      refine ⟨3067818925203631755873523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16361700934419369364658789 3067818925203631755873523)
                      ·
                        rfl

theorem cell23_5974556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_5974556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974556 prefixEnd_5974556 := by exact prefixLift 5974556
  have htrace : WordTrace (prefixWord ++ tailWord_5974556) baseStart_5974556 baseEnd_5974556 := by
    simpa [prefixWord, tailWord_5974556, baseEnd_5974556] using wordTrace_append hprefix tailTrace_5974556
  have hstable : (prefixWord ++ tailWord_5974556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974556).length < 2 ^ (prefixWord ++ tailWord_5974556).sum := by decide
  have hdescent : baseEnd_5974556 < baseStart_5974556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974576 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 3]
def baseStart_5974576 : Nat := 118140960795 + 5974576 * 2 ^ 59
def prefixEnd_5974576 : Nat := 4983230072969 + 3 ^ 40 * 5974576 * 2
def baseEnd_5974576 : Nat := 3067829194816721677623431

theorem tailTrace_5974576 : CollatzResearch.WordTrace tailWord_5974576 prefixEnd_5974576 3067829194816721677623431 := by
  unfold tailWord_5974576
  simp only [CollatzResearch.WordTrace]
  refine ⟨108955344401569501594799791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145273792535426002126399721 108955344401569501594799791)
  ·
    refine ⟨163433016602354252392199687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108955344401569501594799791 163433016602354252392199687)
    ·
      refine ⟨245149524903531378588299531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163433016602354252392199687 245149524903531378588299531)
      ·
        refine ⟨367724287355297067882449297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245149524903531378588299531 367724287355297067882449297)
        ·
          refine ⟨275793215516472800911836973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367724287355297067882449297 275793215516472800911836973)
          ·
            refine ⟨103422455818677300341938865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275793215516472800911836973 103422455818677300341938865)
            ·
              refine ⟨77566841864007975256454149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103422455818677300341938865 77566841864007975256454149)
              ·
                refine ⟨14543782849501495360585153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77566841864007975256454149 14543782849501495360585153)
                ·
                  refine ⟨10907837137126121520438865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14543782849501495360585153 10907837137126121520438865)
                  ·
                    refine ⟨8180877852844591140329149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10907837137126121520438865 8180877852844591140329149)
                    ·
                      refine ⟨3067829194816721677623431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8180877852844591140329149 3067829194816721677623431)
                      ·
                        rfl

theorem cell23_5974576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 3].length) (baseStart_5974576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974576 prefixEnd_5974576 := by exact prefixLift 5974576
  have htrace : WordTrace (prefixWord ++ tailWord_5974576) baseStart_5974576 baseEnd_5974576 := by
    simpa [prefixWord, tailWord_5974576, baseEnd_5974576] using wordTrace_append hprefix tailTrace_5974576
  have hstable : (prefixWord ++ tailWord_5974576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974576).length < 2 ^ (prefixWord ++ tailWord_5974576).sum := by decide
  have hdescent : baseEnd_5974576 < baseStart_5974576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974579 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 8]
def baseStart_5974579 : Nat := 118140960795 + 5974579 * 2 ^ 59
def prefixEnd_5974579 : Nat := 4983230072969 + 3 ^ 40 * 5974579 * 2
def baseEnd_5974579 : Nat := 340870081695409462876213

theorem tailTrace_5974579 : CollatzResearch.WordTrace tailWord_5974579 prefixEnd_5974579 340870081695409462876213 := by
  unfold tailWord_5974579
  simp only [CollatzResearch.WordTrace]
  refine ⟨217910798222128134701958791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145273865481418756467972527 217910798222128134701958791)
  ·
    refine ⟨326866197333192202052938187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217910798222128134701958791 326866197333192202052938187)
    ·
      refine ⟨490299295999788303079407281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326866197333192202052938187 490299295999788303079407281)
      ·
        refine ⟨367724471999841227309555461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490299295999788303079407281 367724471999841227309555461)
        ·
          refine ⟨68948338499970230120541649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 367724471999841227309555461 68948338499970230120541649)
          ·
            refine ⟨51711253874977672590406237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68948338499970230120541649 51711253874977672590406237)
            ·
              refine ⟨19391720203116627221402339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51711253874977672590406237 19391720203116627221402339)
              ·
                refine ⟨29087580304674940832103509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19391720203116627221402339 29087580304674940832103509)
                ·
                  refine ⟨340870081695409462876213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29087580304674940832103509 340870081695409462876213)
                  ·
                    rfl

theorem cell23_5974579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 8].length) (baseStart_5974579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974579 prefixEnd_5974579 := by exact prefixLift 5974579
  have htrace : WordTrace (prefixWord ++ tailWord_5974579) baseStart_5974579 baseEnd_5974579 := by
    simpa [prefixWord, tailWord_5974579, baseEnd_5974579] using wordTrace_append hprefix tailTrace_5974579
  have hstable : (prefixWord ++ tailWord_5974579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974579).length < 2 ^ (prefixWord ++ tailWord_5974579).sum := by decide
  have hdescent : baseEnd_5974579 < baseStart_5974579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974583 : List Nat := [1, 1, 3, 1, 2, 3, 1, 6, 1, 4]
def baseStart_5974583 : Nat := 118140960795 + 5974583 * 2 ^ 59
def prefixEnd_5974583 : Nat := 4983230072969 + 3 ^ 40 * 5974583 * 2
def baseEnd_5974583 : Nat := 1022610929727101050078633

theorem tailTrace_5974583 : CollatzResearch.WordTrace tailWord_5974583 prefixEnd_5974583 1022610929727101050078633 := by
  unfold tailWord_5974583
  simp only [CollatzResearch.WordTrace]
  refine ⟨217910944114113643385104403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145273962742742428923402935 217910944114113643385104403)
  ·
    refine ⟨326866416171170465077656605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217910944114113643385104403 326866416171170465077656605)
    ·
      refine ⟨122574906064188924404121227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326866416171170465077656605 122574906064188924404121227)
      ·
        refine ⟨183862359096283386606181841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122574906064188924404121227 183862359096283386606181841)
        ·
          refine ⟨137896769322212539954636381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183862359096283386606181841 137896769322212539954636381)
          ·
            refine ⟨51711288495829702482988643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137896769322212539954636381 51711288495829702482988643)
            ·
              refine ⟨77566932743744553724482965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51711288495829702482988643 77566932743744553724482965)
              ·
                refine ⟨3635949972363025955835139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77566932743744553724482965 3635949972363025955835139)
                ·
                  refine ⟨5453924958544538933752709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3635949972363025955835139 5453924958544538933752709)
                  ·
                    refine ⟨1022610929727101050078633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5453924958544538933752709 1022610929727101050078633)
                    ·
                      rfl

theorem cell23_5974583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 1, 4].length) (baseStart_5974583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974583 prefixEnd_5974583 := by exact prefixLift 5974583
  have htrace : WordTrace (prefixWord ++ tailWord_5974583) baseStart_5974583 baseEnd_5974583 := by
    simpa [prefixWord, tailWord_5974583, baseEnd_5974583] using wordTrace_append hprefix tailTrace_5974583
  have hstable : (prefixWord ++ tailWord_5974583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974583).length < 2 ^ (prefixWord ++ tailWord_5974583).sum := by decide
  have hdescent : baseEnd_5974583 < baseStart_5974583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974660 : List Nat := [2, 3, 2, 1, 3, 3, 1, 2, 1, 5]
def baseStart_5974660 : Nat := 118140960795 + 5974660 * 2 ^ 59
def prefixEnd_5974660 : Nat := 4983230072969 + 3 ^ 40 * 5974660 * 2
def baseEnd_5974660 : Nat := 1022624109063899782991015

theorem tailTrace_5974660 : CollatzResearch.WordTrace tailWord_5974660 prefixEnd_5974660 1022624109063899782991015 := by
  unfold tailWord_5974660
  simp only [CollatzResearch.WordTrace]
  refine ⟨108956876267417342767828717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145275835023223123690438289 108956876267417342767828717)
  ·
    refine ⟨40858828600281503537935769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108956876267417342767828717 40858828600281503537935769)
    ·
      refine ⟨30644121450211127653451827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40858828600281503537935769 30644121450211127653451827)
      ·
        refine ⟨45966182175316691480177741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30644121450211127653451827 45966182175316691480177741)
        ·
          refine ⟨17237318315743759305066653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45966182175316691480177741 17237318315743759305066653)
          ·
            refine ⟨6463994368403909739399995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17237318315743759305066653 6463994368403909739399995)
            ·
              refine ⟨9695991552605864609099993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6463994368403909739399995 9695991552605864609099993)
              ·
                refine ⟨7271993664454398456824995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9695991552605864609099993 7271993664454398456824995)
                ·
                  refine ⟨10907990496681597685237493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7271993664454398456824995 10907990496681597685237493)
                  ·
                    refine ⟨1022624109063899782991015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10907990496681597685237493 1022624109063899782991015)
                    ·
                      rfl

theorem cell23_5974660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_5974660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974660 prefixEnd_5974660 := by exact prefixLift 5974660
  have htrace : WordTrace (prefixWord ++ tailWord_5974660) baseStart_5974660 baseEnd_5974660 := by
    simpa [prefixWord, tailWord_5974660, baseEnd_5974660] using wordTrace_append hprefix tailTrace_5974660
  have hstable : (prefixWord ++ tailWord_5974660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974660).length < 2 ^ (prefixWord ++ tailWord_5974660).sum := by decide
  have hdescent : baseEnd_5974660 < baseStart_5974660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974680 : List Nat := [2, 1, 2, 4, 1, 1, 5, 1, 1, 1, 4]
def baseStart_5974680 : Nat := 118140960795 + 5974680 * 2 ^ 59
def prefixEnd_5974680 : Nat := 4983230072969 + 3 ^ 40 * 5974680 * 2
def baseEnd_5974680 : Nat := 3067882596804789270722953

theorem tailTrace_5974680 : CollatzResearch.WordTrace tailWord_5974680 prefixEnd_5974680 3067882596804789270722953 := by
  unfold tailWord_5974680
  simp only [CollatzResearch.WordTrace]
  refine ⟨108957240997381114475692747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145276321329841485967590329 108957240997381114475692747)
  ·
    refine ⟨163435861496071671713539121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108957240997381114475692747 163435861496071671713539121)
    ·
      refine ⟨122576896122053753785154341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163435861496071671713539121 122576896122053753785154341)
      ·
        refine ⟨22983168022885078834716439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122576896122053753785154341 22983168022885078834716439)
        ·
          refine ⟨34474752034327618252074659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22983168022885078834716439 34474752034327618252074659)
          ·
            refine ⟨51712128051491427378111989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34474752034327618252074659 51712128051491427378111989)
            ·
              refine ⟨4848012004827321316697999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51712128051491427378111989 4848012004827321316697999)
              ·
                refine ⟨7272018007240981975046999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4848012004827321316697999 7272018007240981975046999)
                ·
                  refine ⟨10908027010861472962570499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7272018007240981975046999 10908027010861472962570499)
                  ·
                    refine ⟨16362040516292209443855749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10908027010861472962570499 16362040516292209443855749)
                    ·
                      refine ⟨3067882596804789270722953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16362040516292209443855749 3067882596804789270722953)
                      ·
                        rfl

theorem cell23_5974680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_5974680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974680 prefixEnd_5974680 := by exact prefixLift 5974680
  have htrace : WordTrace (prefixWord ++ tailWord_5974680) baseStart_5974680 baseEnd_5974680 := by
    simpa [prefixWord, tailWord_5974680, baseEnd_5974680] using wordTrace_append hprefix tailTrace_5974680
  have hstable : (prefixWord ++ tailWord_5974680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974680).length < 2 ^ (prefixWord ++ tailWord_5974680).sum := by decide
  have hdescent : baseEnd_5974680 < baseStart_5974680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974713 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 6, 1, 3]
def baseStart_5974713 : Nat := 118140960795 + 5974713 * 2 ^ 59
def prefixEnd_5974713 : Nat := 4983230072969 + 3 ^ 40 * 5974713 * 2
def baseEnd_5974713 : Nat := 3067899541666387641610301

theorem tailTrace_5974713 : CollatzResearch.WordTrace tailWord_5974713 prefixEnd_5974713 3067899541666387641610301 := by
  unfold tailWord_5974713
  simp only [CollatzResearch.WordTrace]
  refine ⟨217915685603642675587336793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145277123735761783724891195 217915685603642675587336793)
  ·
    refine ⟨163436764202732006690502595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217915685603642675587336793 163436764202732006690502595)
    ·
      refine ⟨245155146304098010035753893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163436764202732006690502595 245155146304098010035753893)
      ·
        refine ⟨45966589932018376881703855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245155146304098010035753893 45966589932018376881703855)
        ·
          refine ⟨68949884898027565322555783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45966589932018376881703855 68949884898027565322555783)
          ·
            refine ⟨103424827347041347983833675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68949884898027565322555783 103424827347041347983833675)
            ·
              refine ⟨155137241020562021975750513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103424827347041347983833675 155137241020562021975750513)
              ·
                refine ⟨116352930765421516481812885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155137241020562021975750513 116352930765421516481812885)
                ·
                  refine ⟨5454043629629133585084979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116352930765421516481812885 5454043629629133585084979)
                  ·
                    refine ⟨8181065444443700377627469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5454043629629133585084979 8181065444443700377627469)
                    ·
                      refine ⟨3067899541666387641610301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8181065444443700377627469 3067899541666387641610301)
                      ·
                        rfl

theorem cell23_5974713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_5974713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974713 prefixEnd_5974713 := by exact prefixLift 5974713
  have htrace : WordTrace (prefixWord ++ tailWord_5974713) baseStart_5974713 baseEnd_5974713 := by
    simpa [prefixWord, tailWord_5974713, baseEnd_5974713] using wordTrace_append hprefix tailTrace_5974713
  have hstable : (prefixWord ++ tailWord_5974713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974713).length < 2 ^ (prefixWord ++ tailWord_5974713).sum := by decide
  have hdescent : baseEnd_5974713 < baseStart_5974713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974716 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 2, 7]
def baseStart_5974716 : Nat := 118140960795 + 5974716 * 2 ^ 59
def prefixEnd_5974716 : Nat := 4983230072969 + 3 ^ 40 * 5974716 * 2
def baseEnd_5974716 : Nat := 1022633694036117043290929

theorem tailTrace_5974716 : CollatzResearch.WordTrace tailWord_5974716 prefixEnd_5974716 1022633694036117043290929 := by
  unfold tailWord_5974716
  simp only [CollatzResearch.WordTrace]
  refine ⟨108957897511315903549848001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145277196681754538066464001 108957897511315903549848001)
  ·
    refine ⟨81718423133486927662386001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108957897511315903549848001 81718423133486927662386001)
    ·
      refine ⟨61288817350115195746789501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81718423133486927662386001 61288817350115195746789501)
      ·
        refine ⟨22983306506293198405046063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61288817350115195746789501 22983306506293198405046063)
        ·
          refine ⟨34474959759439797607569095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22983306506293198405046063 34474959759439797607569095)
          ·
            refine ⟨51712439639159696411353643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34474959759439797607569095 51712439639159696411353643)
            ·
              refine ⟨77568659458739544617030465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51712439639159696411353643 77568659458739544617030465)
              ·
                refine ⟨58176494594054658462772849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77568659458739544617030465 58176494594054658462772849)
                ·
                  refine ⟨43632370945540993847079637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58176494594054658462772849 43632370945540993847079637)
                  ·
                    refine ⟨1022633694036117043290929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43632370945540993847079637 1022633694036117043290929)
                    ·
                      rfl

theorem cell23_5974716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_5974716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974716 prefixEnd_5974716 := by exact prefixLift 5974716
  have htrace : WordTrace (prefixWord ++ tailWord_5974716) baseStart_5974716 baseEnd_5974716 := by
    simpa [prefixWord, tailWord_5974716, baseEnd_5974716] using wordTrace_append hprefix tailTrace_5974716
  have hstable : (prefixWord ++ tailWord_5974716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974716).length < 2 ^ (prefixWord ++ tailWord_5974716).sum := by decide
  have hdescent : baseEnd_5974716 < baseStart_5974716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974746 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 4, 6]
def baseStart_5974746 : Nat := 118140960795 + 5974746 * 2 ^ 59
def prefixEnd_5974746 : Nat := 4983230072969 + 3 ^ 40 * 5974746 * 2
def baseEnd_5974746 : Nat := 1022638828842662004165883

theorem tailTrace_5974746 : CollatzResearch.WordTrace tailWord_5974746 prefixEnd_5974746 1022638828842662004165883 := by
  unfold tailWord_5974746
  simp only [CollatzResearch.WordTrace]
  refine ⟨54479222303130780555822023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145277926141682081482192061 54479222303130780555822023)
  ·
    refine ⟨81718833454696170833733035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54479222303130780555822023 81718833454696170833733035)
    ·
      refine ⟨122578250182044256250599553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81718833454696170833733035 122578250182044256250599553)
      ·
        refine ⟨91933687636533192187949665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122578250182044256250599553 91933687636533192187949665)
        ·
          refine ⟨68950265727399894140962249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91933687636533192187949665 68950265727399894140962249)
          ·
            refine ⟨51712699295549920605721687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68950265727399894140962249 51712699295549920605721687)
            ·
              refine ⟨77569048943324880908582531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51712699295549920605721687 77569048943324880908582531)
              ·
                refine ⟨116353573414987321362873797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77569048943324880908582531 116353573414987321362873797)
                ·
                  refine ⟨21816295015310122755538837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116353573414987321362873797 21816295015310122755538837)
                  ·
                    refine ⟨1022638828842662004165883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21816295015310122755538837 1022638828842662004165883)
                    ·
                      rfl

theorem cell23_5974746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_5974746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974746 prefixEnd_5974746 := by exact prefixLift 5974746
  have htrace : WordTrace (prefixWord ++ tailWord_5974746) baseStart_5974746 baseEnd_5974746 := by
    simpa [prefixWord, tailWord_5974746, baseEnd_5974746] using wordTrace_append hprefix tailTrace_5974746
  have hstable : (prefixWord ++ tailWord_5974746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974746).length < 2 ^ (prefixWord ++ tailWord_5974746).sum := by decide
  have hdescent : baseEnd_5974746 < baseStart_5974746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974776 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 7]
def baseStart_5974776 : Nat := 118140960795 + 5974776 * 2 ^ 59
def prefixEnd_5974776 : Nat := 4983230072969 + 3 ^ 40 * 5974776 * 2
def baseEnd_5974776 : Nat := 340881321216402321680279

theorem tailTrace_5974776 : CollatzResearch.WordTrace tailWord_5974776 prefixEnd_5974776 340881321216402321680279 := by
  unfold tailWord_5974776
  simp only [CollatzResearch.WordTrace]
  refine ⟨108958991701207218673440091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145278655601609624897920121 108958991701207218673440091)
  ·
    refine ⟨163438487551810828010160137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108958991701207218673440091 163438487551810828010160137)
    ·
      refine ⟨122578865663858121007620103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163438487551810828010160137 122578865663858121007620103)
      ·
        refine ⟨183868298495787181511430155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122578865663858121007620103 183868298495787181511430155)
        ·
          refine ⟨275802447743680772267145233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183868298495787181511430155 275802447743680772267145233)
          ·
            refine ⟨206851835807760579200358925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275802447743680772267145233 206851835807760579200358925)
            ·
              refine ⟨77569438427910217200134597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206851835807760579200358925 77569438427910217200134597)
              ·
                refine ⟨14544269705233165725025237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77569438427910217200134597 14544269705233165725025237)
                ·
                  refine ⟨340881321216402321680279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14544269705233165725025237 340881321216402321680279)
                  ·
                    rfl

theorem cell23_5974776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 7].length) (baseStart_5974776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974776 prefixEnd_5974776 := by exact prefixLift 5974776
  have htrace : WordTrace (prefixWord ++ tailWord_5974776) baseStart_5974776 baseEnd_5974776 := by
    simpa [prefixWord, tailWord_5974776, baseEnd_5974776] using wordTrace_append hprefix tailTrace_5974776
  have hstable : (prefixWord ++ tailWord_5974776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974776).length < 2 ^ (prefixWord ++ tailWord_5974776).sum := by decide
  have hdescent : baseEnd_5974776 < baseStart_5974776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974853 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 7, 4]
def baseStart_5974853 : Nat := 118140960795 + 5974853 * 2 ^ 59
def prefixEnd_5974853 : Nat := 4983230072969 + 3 ^ 40 * 5974853 * 2
def baseEnd_5974853 : Nat := 1022657142986005697953219

theorem tailTrace_5974853 : CollatzResearch.WordTrace tailWord_5974853 prefixEnd_5974853 1022657142986005697953219 := by
  unfold tailWord_5974853
  simp only [CollatzResearch.WordTrace]
  refine ⟨217920791823135479497433213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145280527882090319664955475 217920791823135479497433213)
  ·
    refine ⟨81720296933675804811537455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217920791823135479497433213 81720296933675804811537455)
    ·
      refine ⟨122580445400513707217306183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81720296933675804811537455 122580445400513707217306183)
      ·
        refine ⟨183870668100770560825959275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122580445400513707217306183 183870668100770560825959275)
        ·
          refine ⟨275806002151155841238938913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183870668100770560825959275 275806002151155841238938913)
          ·
            refine ⟨206854501613366880929204185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275806002151155841238938913 206854501613366880929204185)
            ·
              refine ⟨155140876210025160696903139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206854501613366880929204185 155140876210025160696903139)
              ·
                refine ⟨232711314315037741045354709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155140876210025160696903139 232711314315037741045354709)
                ·
                  refine ⟨5454171429258697055750501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 232711314315037741045354709 5454171429258697055750501)
                  ·
                    refine ⟨1022657142986005697953219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5454171429258697055750501 1022657142986005697953219)
                    ·
                      rfl

theorem cell23_5974853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_5974853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974853 prefixEnd_5974853 := by exact prefixLift 5974853
  have htrace : WordTrace (prefixWord ++ tailWord_5974853) baseStart_5974853 baseEnd_5974853 := by
    simpa [prefixWord, tailWord_5974853, baseEnd_5974853] using wordTrace_append hprefix tailTrace_5974853
  have hstable : (prefixWord ++ tailWord_5974853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974853).length < 2 ^ (prefixWord ++ tailWord_5974853).sum := by decide
  have hdescent : baseEnd_5974853 < baseStart_5974853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974860 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 2, 1, 4]
def baseStart_5974860 : Nat := 118140960795 + 5974860 * 2 ^ 59
def prefixEnd_5974860 : Nat := 4983230072969 + 3 ^ 40 * 5974860 * 2
def baseEnd_5974860 : Nat := 3067975023322598566472125

theorem tailTrace_5974860 : CollatzResearch.WordTrace tailWord_5974860 prefixEnd_5974860 3067975023322598566472125 := by
  unfold tailWord_5974860
  simp only [CollatzResearch.WordTrace]
  refine ⟨108960523567055059846469017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145280698089406746461958689 108960523567055059846469017)
  ·
    refine ⟨81720392675291294884851763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108960523567055059846469017 81720392675291294884851763)
    ·
      refine ⟨122580589012936942327277645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81720392675291294884851763 122580589012936942327277645)
      ·
        refine ⟨45967720879851353372729117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122580589012936942327277645 45967720879851353372729117)
        ·
          refine ⟨17237895329944257514773419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45967720879851353372729117 17237895329944257514773419)
          ·
            refine ⟨25856842994916386272160129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17237895329944257514773419 25856842994916386272160129)
            ·
              refine ⟨19392632246187289704120097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25856842994916386272160129 19392632246187289704120097)
              ·
                refine ⟨14544474184640467278090073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19392632246187289704120097 14544474184640467278090073)
                ·
                  refine ⟨10908355638480350458567555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14544474184640467278090073 10908355638480350458567555)
                  ·
                    refine ⟨16362533457720525687851333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10908355638480350458567555 16362533457720525687851333)
                    ·
                      refine ⟨3067975023322598566472125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16362533457720525687851333 3067975023322598566472125)
                      ·
                        rfl

theorem cell23_5974860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_5974860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974860 prefixEnd_5974860 := by exact prefixLift 5974860
  have htrace : WordTrace (prefixWord ++ tailWord_5974860) baseStart_5974860 baseEnd_5974860 := by
    simpa [prefixWord, tailWord_5974860, baseEnd_5974860] using wordTrace_append hprefix tailTrace_5974860
  have hstable : (prefixWord ++ tailWord_5974860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974860).length < 2 ^ (prefixWord ++ tailWord_5974860).sum := by decide
  have hdescent : baseEnd_5974860 < baseStart_5974860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974861 : List Nat := [1, 6, 1, 2, 2, 2, 2, 2, 5]
def baseStart_5974861 : Nat := 118140960795 + 5974861 * 2 ^ 59
def prefixEnd_5974861 : Nat := 4983230072969 + 3 ^ 40 * 5974861 * 2
def baseEnd_5974861 : Nat := 340886170755917006951069

theorem tailTrace_5974861 : CollatzResearch.WordTrace tailWord_5974861 prefixEnd_5974861 340886170755917006951069 := by
  unfold tailWord_5974861
  simp only [CollatzResearch.WordTrace]
  refine ⟨217921083607106496863724437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145280722404737664575816291 217921083607106496863724437)
  ·
    refine ⟨10215050794083117040487083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 217921083607106496863724437 10215050794083117040487083)
    ·
      refine ⟨15322576191124675560730625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10215050794083117040487083 15322576191124675560730625)
      ·
        refine ⟨11491932143343506670547969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15322576191124675560730625 11491932143343506670547969)
        ·
          refine ⟨8618949107507630002910977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11491932143343506670547969 8618949107507630002910977)
          ·
            refine ⟨6464211830630722502183233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8618949107507630002910977 6464211830630722502183233)
            ·
              refine ⟨4848158872973041876637425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6464211830630722502183233 4848158872973041876637425)
              ·
                refine ⟨3636119154729781407478069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4848158872973041876637425 3636119154729781407478069)
                ·
                  refine ⟨340886170755917006951069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3636119154729781407478069 340886170755917006951069)
                  ·
                    rfl

theorem cell23_5974861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_5974861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974861 prefixEnd_5974861 := by exact prefixLift 5974861
  have htrace : WordTrace (prefixWord ++ tailWord_5974861) baseStart_5974861 baseEnd_5974861 := by
    simpa [prefixWord, tailWord_5974861, baseEnd_5974861] using wordTrace_append hprefix tailTrace_5974861
  have hstable : (prefixWord ++ tailWord_5974861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974861).length < 2 ^ (prefixWord ++ tailWord_5974861).sum := by decide
  have hdescent : baseEnd_5974861 < baseStart_5974861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974894 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_5974894 : Nat := 118140960795 + 5974894 * 2 ^ 59
def prefixEnd_5974894 : Nat := 4983230072969 + 3 ^ 40 * 5974894 * 2
def baseEnd_5974894 : Nat := 3067992481664851433446969

theorem tailTrace_5974894 : CollatzResearch.WordTrace tailWord_5974894 prefixEnd_5974894 3067992481664851433446969 := by
  unfold tailWord_5974894
  simp only [CollatzResearch.WordTrace]
  refine ⟨27240285901998367937459467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145281524810657962333117157 27240285901998367937459467)
  ·
    refine ⟨40860428852997551906189201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27240285901998367937459467 40860428852997551906189201)
    ·
      refine ⟨30645321639748163929641901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40860428852997551906189201 30645321639748163929641901)
      ·
        refine ⟨11491995614905561473615713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30645321639748163929641901 11491995614905561473615713)
        ·
          refine ⟨8618996711179171105211785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11491995614905561473615713 8618996711179171105211785)
          ·
            refine ⟨6464247533384378328908839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8618996711179171105211785 6464247533384378328908839)
            ·
              refine ⟨9696371300076567493363259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6464247533384378328908839 9696371300076567493363259)
              ·
                refine ⟨14544556950114851240044889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9696371300076567493363259 14544556950114851240044889)
                ·
                  refine ⟨10908417712586138430033667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14544556950114851240044889 10908417712586138430033667)
                  ·
                    refine ⟨16362626568879207645050501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10908417712586138430033667 16362626568879207645050501)
                    ·
                      refine ⟨3067992481664851433446969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16362626568879207645050501 3067992481664851433446969)
                      ·
                        rfl

theorem cell23_5974894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_5974894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974894 prefixEnd_5974894 := by exact prefixLift 5974894
  have htrace : WordTrace (prefixWord ++ tailWord_5974894) baseStart_5974894 baseEnd_5974894 := by
    simpa [prefixWord, tailWord_5974894, baseEnd_5974894] using wordTrace_append hprefix tailTrace_5974894
  have hstable : (prefixWord ++ tailWord_5974894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974894).length < 2 ^ (prefixWord ++ tailWord_5974894).sum := by decide
  have hdescent : baseEnd_5974894 < baseStart_5974894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974897 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 2, 2, 3]
def baseStart_5974897 : Nat := 118140960795 + 5974897 * 2 ^ 59
def prefixEnd_5974897 : Nat := 4983230072969 + 3 ^ 40 * 5974897 * 2
def baseEnd_5974897 : Nat := 3067994022106814921709455

theorem tailTrace_5974897 : CollatzResearch.WordTrace tailWord_5974897 prefixEnd_5974897 3067994022106814921709455 := by
  unfold tailWord_5974897
  simp only [CollatzResearch.WordTrace]
  refine ⟨217922396634976075012034945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145281597756650716674689963 217922396634976075012034945)
  ·
    refine ⟨163441797476232056259026209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217922396634976075012034945 163441797476232056259026209)
    ·
      refine ⟨122581348107174042194269657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163441797476232056259026209 122581348107174042194269657)
      ·
        refine ⟨91936011080380531645702243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122581348107174042194269657 91936011080380531645702243)
        ·
          refine ⟨137904016620570797468553365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91936011080380531645702243 137904016620570797468553365)
          ·
            refine ⟨6464250779089256131338439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 137904016620570797468553365 6464250779089256131338439)
            ·
              refine ⟨9696376168633884197007659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6464250779089256131338439 9696376168633884197007659)
              ·
                refine ⟨14544564252950826295511489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9696376168633884197007659 14544564252950826295511489)
                ·
                  refine ⟨10908423189713119721633617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14544564252950826295511489 10908423189713119721633617)
                  ·
                    refine ⟨8181317392284839791225213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10908423189713119721633617 8181317392284839791225213)
                    ·
                      refine ⟨3067994022106814921709455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8181317392284839791225213 3067994022106814921709455)
                      ·
                        rfl

theorem cell23_5974897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_5974897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974897 prefixEnd_5974897 := by exact prefixLift 5974897
  have htrace : WordTrace (prefixWord ++ tailWord_5974897) baseStart_5974897 baseEnd_5974897 := by
    simpa [prefixWord, tailWord_5974897, baseEnd_5974897] using wordTrace_append hprefix tailTrace_5974897
  have hstable : (prefixWord ++ tailWord_5974897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974897).length < 2 ^ (prefixWord ++ tailWord_5974897).sum := by decide
  have hdescent : baseEnd_5974897 < baseStart_5974897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974953 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 3, 1, 5]
def baseStart_5974953 : Nat := 118140960795 + 5974953 * 2 ^ 59
def prefixEnd_5974953 : Nat := 4983230072969 + 3 ^ 40 * 5974953 * 2
def baseEnd_5974953 : Nat := 3068022777023466702609197

theorem tailTrace_5974953 : CollatzResearch.WordTrace tailWord_5974953 prefixEnd_5974953 3068022777023466702609197 := by
  unfold tailWord_5974953
  simp only [CollatzResearch.WordTrace]
  refine ⟨217924439122773196576073513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145282959415182131050715675 217924439122773196576073513)
  ·
    refine ⟨163443329342079897432055135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217924439122773196576073513 163443329342079897432055135)
    ·
      refine ⟨245164994013119846148082703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163443329342079897432055135 245164994013119846148082703)
      ·
        refine ⟨367747491019679769222124055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245164994013119846148082703 367747491019679769222124055)
        ·
          refine ⟨551621236529519653833186083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367747491019679769222124055 551621236529519653833186083)
          ·
            refine ⟨827431854794279480749779125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551621236529519653833186083 827431854794279480749779125)
            ·
              refine ⟨77571736386963701320291793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 827431854794279480749779125 77571736386963701320291793)
              ·
                refine ⟨58178802290222775990218845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77571736386963701320291793 58178802290222775990218845)
                ·
                  refine ⟨21817050858833540996332067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58178802290222775990218845 21817050858833540996332067)
                  ·
                    refine ⟨32725576288250311494498101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21817050858833540996332067 32725576288250311494498101)
                    ·
                      refine ⟨3068022777023466702609197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32725576288250311494498101 3068022777023466702609197)
                      ·
                        rfl

theorem cell23_5974953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_5974953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974953 prefixEnd_5974953 := by exact prefixLift 5974953
  have htrace : WordTrace (prefixWord ++ tailWord_5974953) baseStart_5974953 baseEnd_5974953 := by
    simpa [prefixWord, tailWord_5974953, baseEnd_5974953] using wordTrace_append hprefix tailTrace_5974953
  have hstable : (prefixWord ++ tailWord_5974953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974953).length < 2 ^ (prefixWord ++ tailWord_5974953).sum := by decide
  have hdescent : baseEnd_5974953 < baseStart_5974953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974964 : List Nat := [2, 5, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_5974964 : Nat := 118140960795 + 5974964 * 2 ^ 59
def prefixEnd_5974964 : Nat := 4983230072969 + 3 ^ 40 * 5974964 * 2
def baseEnd_5974964 : Nat := 1022676141770222053190549

theorem tailTrace_5974964 : CollatzResearch.WordTrace tailWord_5974964 prefixEnd_5974964 1022676141770222053190549 := by
  unfold tailWord_5974964
  simp only [CollatzResearch.WordTrace]
  refine ⟨108962420162866672727361973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145283226883822230303149297 108962420162866672727361973)
  ·
    refine ⟨10215226890268750568190185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108962420162866672727361973 10215226890268750568190185)
    ·
      refine ⟨7661420167701562926142639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10215226890268750568190185 7661420167701562926142639)
      ·
        refine ⟨11492130251552344389213959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7661420167701562926142639 11492130251552344389213959)
        ·
          refine ⟨17238195377328516583820939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11492130251552344389213959 17238195377328516583820939)
          ·
            refine ⟨25857293065992774875731409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17238195377328516583820939 25857293065992774875731409)
            ·
              refine ⟨19392969799494581156798557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25857293065992774875731409 19392969799494581156798557)
              ·
                refine ⟨7272363674810467933799459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19392969799494581156798557 7272363674810467933799459)
                ·
                  refine ⟨10908545512215701900699189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7272363674810467933799459 10908545512215701900699189)
                  ·
                    refine ⟨1022676141770222053190549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10908545512215701900699189 1022676141770222053190549)
                    ·
                      rfl

theorem cell23_5974964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_5974964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974964 prefixEnd_5974964 := by exact prefixLift 5974964
  have htrace : WordTrace (prefixWord ++ tailWord_5974964) baseStart_5974964 baseEnd_5974964 := by
    simpa [prefixWord, tailWord_5974964, baseEnd_5974964] using wordTrace_append hprefix tailTrace_5974964
  have hstable : (prefixWord ++ tailWord_5974964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974964).length < 2 ^ (prefixWord ++ tailWord_5974964).sum := by decide
  have hdescent : baseEnd_5974964 < baseStart_5974964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974967 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 5, 2, 2]
def baseStart_5974967 : Nat := 118140960795 + 5974967 * 2 ^ 59
def prefixEnd_5974967 : Nat := 4983230072969 + 3 ^ 40 * 5974967 * 2
def baseEnd_5974967 : Nat := 3068029965752629647834133

theorem tailTrace_5974967 : CollatzResearch.WordTrace tailWord_5974967 prefixEnd_5974967 3068029965752629647834133 := by
  unfold tailWord_5974967
  simp only [CollatzResearch.WordTrace]
  refine ⟨217924949744722476967083155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145283299829814984644722103 217924949744722476967083155)
  ·
    refine ⟨326887424617083715450624733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217924949744722476967083155 326887424617083715450624733)
    ·
      refine ⟨122582784231406393293984275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326887424617083715450624733 122582784231406393293984275)
      ·
        refine ⟨183874176347109589940976413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122582784231406393293984275 183874176347109589940976413)
        ·
          refine ⟨68952816130166096227866155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183874176347109589940976413 68952816130166096227866155)
          ·
            refine ⟨103429224195249144341799233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68952816130166096227866155 103429224195249144341799233)
            ·
              refine ⟨77571918146436858256349425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103429224195249144341799233 77571918146436858256349425)
              ·
                refine ⟨58178938609827643692262069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77571918146436858256349425 58178938609827643692262069)
                ·
                  refine ⟨5454275494671341596149569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58178938609827643692262069 5454275494671341596149569)
                  ·
                    refine ⟨4090706621003506197112177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5454275494671341596149569 4090706621003506197112177)
                    ·
                      refine ⟨3068029965752629647834133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4090706621003506197112177 3068029965752629647834133)
                      ·
                        rfl

theorem cell23_5974967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 2, 2].length) (baseStart_5974967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974967 prefixEnd_5974967 := by exact prefixLift 5974967
  have htrace : WordTrace (prefixWord ++ tailWord_5974967) baseStart_5974967 baseEnd_5974967 := by
    simpa [prefixWord, tailWord_5974967, baseEnd_5974967] using wordTrace_append hprefix tailTrace_5974967
  have hstable : (prefixWord ++ tailWord_5974967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974967).length < 2 ^ (prefixWord ++ tailWord_5974967).sum := by decide
  have hdescent : baseEnd_5974967 < baseStart_5974967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974970 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5]
def baseStart_5974970 : Nat := 118140960795 + 5974970 * 2 ^ 59
def prefixEnd_5974970 : Nat := 4983230072969 + 3 ^ 40 * 5974970 * 2
def baseEnd_5974970 : Nat := 3068031506194593136096619

theorem tailTrace_5974970 : CollatzResearch.WordTrace tailWord_5974970 prefixEnd_5974970 3068031506194593136096619 := by
  unfold tailWord_5974970
  simp only [CollatzResearch.WordTrace]
  refine ⟨54481264790927902119860591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145283372775807738986294909 54481264790927902119860591)
  ·
    refine ⟨81721897186391853179790887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54481264790927902119860591 81721897186391853179790887)
    ·
      refine ⟨122582845779587779769686331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81721897186391853179790887 122582845779587779769686331)
      ·
        refine ⟨183874268669381669654529497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122582845779587779769686331 183874268669381669654529497)
        ·
          refine ⟨137905701502036252240897123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183874268669381669654529497 137905701502036252240897123)
          ·
            refine ⟨206858552253054378361345685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137905701502036252240897123 206858552253054378361345685)
            ·
              refine ⟨9696494636861923985688079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 206858552253054378361345685 9696494636861923985688079)
              ·
                refine ⟨14544741955292885978532119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9696494636861923985688079 14544741955292885978532119)
                ·
                  refine ⟨21817112932939328967798179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14544741955292885978532119 21817112932939328967798179)
                  ·
                    refine ⟨32725669399408993451697269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21817112932939328967798179 32725669399408993451697269)
                    ·
                      refine ⟨3068031506194593136096619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32725669399408993451697269 3068031506194593136096619)
                      ·
                        rfl

theorem cell23_5974970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_5974970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974970 prefixEnd_5974970 := by exact prefixLift 5974970
  have htrace : WordTrace (prefixWord ++ tailWord_5974970) baseStart_5974970 baseEnd_5974970 := by
    simpa [prefixWord, tailWord_5974970, baseEnd_5974970] using wordTrace_append hprefix tailTrace_5974970
  have hstable : (prefixWord ++ tailWord_5974970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974970).length < 2 ^ (prefixWord ++ tailWord_5974970).sum := by decide
  have hdescent : baseEnd_5974970 < baseStart_5974970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974990 : List Nat := [4, 1, 1, 1, 2, 4, 2, 8]
def baseStart_5974990 : Nat := 118140960795 + 5974990 * 2 ^ 59
def prefixEnd_5974990 : Nat := 4983230072969 + 3 ^ 40 * 5974990 * 2
def baseEnd_5974990 : Nat := 113631176881766039179501

theorem tailTrace_5974990 : CollatzResearch.WordTrace tailWord_5974990 prefixEnd_5974990 113631176881766039179501 := by
  unfold tailWord_5974990
  simp only [CollatzResearch.WordTrace]
  refine ⟨27240723577954893986896303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145283859082426101263446949 27240723577954893986896303)
  ·
    refine ⟨40861085366932340980344455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27240723577954893986896303 40861085366932340980344455)
    ·
      refine ⟨61291628050398511470516683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40861085366932340980344455 61291628050398511470516683)
      ·
        refine ⟨91937442075597767205775025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61291628050398511470516683 91937442075597767205775025)
        ·
          refine ⟨68953081556698325404331269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91937442075597767205775025 68953081556698325404331269)
          ·
            refine ⟨12928702791880936013312113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68953081556698325404331269 12928702791880936013312113)
            ·
              refine ⟨9696527093910702009984085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12928702791880936013312113 9696527093910702009984085)
              ·
                refine ⟨113631176881766039179501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9696527093910702009984085 113631176881766039179501)
                ·
                  rfl

theorem cell23_5974990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 8].length) (baseStart_5974990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974990 prefixEnd_5974990 := by exact prefixLift 5974990
  have htrace : WordTrace (prefixWord ++ tailWord_5974990) baseStart_5974990 baseEnd_5974990 := by
    simpa [prefixWord, tailWord_5974990, baseEnd_5974990] using wordTrace_append hprefix tailTrace_5974990
  have hstable : (prefixWord ++ tailWord_5974990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974990).length < 2 ^ (prefixWord ++ tailWord_5974990).sum := by decide
  have hdescent : baseEnd_5974990 < baseStart_5974990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974993 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 2, 2, 6]
def baseStart_5974993 : Nat := 118140960795 + 5974993 * 2 ^ 59
def prefixEnd_5974993 : Nat := 4983230072969 + 3 ^ 40 * 5974993 * 2
def baseEnd_5974993 : Nat := 3068043316249646546109013

theorem tailTrace_5974993 : CollatzResearch.WordTrace tailWord_5974993 prefixEnd_5974993 3068043316249646546109013 := by
  unfold tailWord_5974993
  simp only [CollatzResearch.WordTrace]
  refine ⟨217925898042628283407529633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145283932028418855605019755 217925898042628283407529633)
  ·
    refine ⟨163444423531971212555647225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217925898042628283407529633 163444423531971212555647225)
    ·
      refine ⟨122583317648978409416735419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163444423531971212555647225 122583317648978409416735419)
      ·
        refine ⟨183874976473467614125103129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122583317648978409416735419 183874976473467614125103129)
        ·
          refine ⟨137906232355100710593827347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183874976473467614125103129 137906232355100710593827347)
          ·
            refine ⟨206859348532651065890741021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137906232355100710593827347 206859348532651065890741021)
            ·
              refine ⟨77572255699744149709027883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206859348532651065890741021 77572255699744149709027883)
              ·
                refine ⟨116358383549616224563541825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77572255699744149709027883 116358383549616224563541825)
                ·
                  refine ⟨87268787662212168422656369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116358383549616224563541825 87268787662212168422656369)
                  ·
                    refine ⟨65451590746659126316992277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87268787662212168422656369 65451590746659126316992277)
                    ·
                      refine ⟨3068043316249646546109013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65451590746659126316992277 3068043316249646546109013)
                      ·
                        rfl

theorem cell23_5974993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_5974993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974993 prefixEnd_5974993 := by exact prefixLift 5974993
  have htrace : WordTrace (prefixWord ++ tailWord_5974993) baseStart_5974993 baseEnd_5974993 := by
    simpa [prefixWord, tailWord_5974993, baseEnd_5974993] using wordTrace_append hprefix tailTrace_5974993
  have hstable : (prefixWord ++ tailWord_5974993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974993).length < 2 ^ (prefixWord ++ tailWord_5974993).sum := by decide
  have hdescent : baseEnd_5974993 < baseStart_5974993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5974994 : List Nat := [3, 2, 2, 3, 1, 2, 1, 3, 2, 4]
def baseStart_5974994 : Nat := 118140960795 + 5974994 * 2 ^ 59
def prefixEnd_5974994 : Nat := 4983230072969 + 3 ^ 40 * 5974994 * 2
def baseEnd_5974994 : Nat := 1022681276576767014065503

theorem tailTrace_5974994 : CollatzResearch.WordTrace tailWord_5974994 prefixEnd_5974994 1022681276576767014065503 := by
  unfold tailWord_5974994
  simp only [CollatzResearch.WordTrace]
  refine ⟨54481483628906165144579009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145283956343749773718877357 54481483628906165144579009)
  ·
    refine ⟨40861112721679623858434257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54481483628906165144579009 40861112721679623858434257)
    ·
      refine ⟨30645834541259717893825693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40861112721679623858434257 30645834541259717893825693)
      ·
        refine ⟨11492187952972394210184635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30645834541259717893825693 11492187952972394210184635)
        ·
          refine ⟨17238281929458591315276953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11492187952972394210184635 17238281929458591315276953)
          ·
            refine ⟨12928711447093943486457715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17238281929458591315276953 12928711447093943486457715)
            ·
              refine ⟨19393067170640915229686573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12928711447093943486457715 19393067170640915229686573)
              ·
                refine ⟨7272400188990343211132465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19393067170640915229686573 7272400188990343211132465)
                ·
                  refine ⟨5454300141742757408349349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7272400188990343211132465 5454300141742757408349349)
                  ·
                    refine ⟨1022681276576767014065503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5454300141742757408349349 1022681276576767014065503)
                    ·
                      rfl

theorem cell23_5974994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_5974994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5974994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5974994 prefixEnd_5974994 := by exact prefixLift 5974994
  have htrace : WordTrace (prefixWord ++ tailWord_5974994) baseStart_5974994 baseEnd_5974994 := by
    simpa [prefixWord, tailWord_5974994, baseEnd_5974994] using wordTrace_append hprefix tailTrace_5974994
  have hstable : (prefixWord ++ tailWord_5974994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5974994).length < 2 ^ (prefixWord ++ tailWord_5974994).sum := by decide
  have hdescent : baseEnd_5974994 < baseStart_5974994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5974994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975050 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 1, 8]
def baseStart_5975050 : Nat := 118140960795 + 5975050 * 2 ^ 59
def prefixEnd_5975050 : Nat := 4983230072969 + 3 ^ 40 * 5975050 * 2
def baseEnd_5975050 : Nat := 1022690861548984274365417

theorem tailTrace_5975050 : CollatzResearch.WordTrace tailWord_5975050 prefixEnd_5975050 1022690861548984274365417 := by
  unfold tailWord_5975050
  simp only [CollatzResearch.WordTrace]
  refine ⟨54481994250855445535588651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145285318002281188094903069 54481994250855445535588651)
  ·
    refine ⟨81722991376283168303382977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54481994250855445535588651 81722991376283168303382977)
    ·
      refine ⟨61292243532212376227537233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81722991376283168303382977 61292243532212376227537233)
      ·
        refine ⟨45969182649159282170652925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61292243532212376227537233 45969182649159282170652925)
        ·
          refine ⟨17238443493434730813994847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45969182649159282170652925 17238443493434730813994847)
          ·
            refine ⟨25857665240152096220992271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17238443493434730813994847 25857665240152096220992271)
            ·
              refine ⟨38786497860228144331488407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25857665240152096220992271 38786497860228144331488407)
              ·
                refine ⟨58179746790342216497232611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38786497860228144331488407 58179746790342216497232611)
                ·
                  refine ⟨87269620185513324745848917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58179746790342216497232611 87269620185513324745848917)
                  ·
                    refine ⟨1022690861548984274365417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87269620185513324745848917 1022690861548984274365417)
                    ·
                      rfl

theorem cell23_5975050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_5975050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975050 prefixEnd_5975050 := by exact prefixLift 5975050
  have htrace : WordTrace (prefixWord ++ tailWord_5975050) baseStart_5975050 baseEnd_5975050 := by
    simpa [prefixWord, tailWord_5975050, baseEnd_5975050] using wordTrace_append hprefix tailTrace_5975050
  have hstable : (prefixWord ++ tailWord_5975050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975050).length < 2 ^ (prefixWord ++ tailWord_5975050).sum := by decide
  have hdescent : baseEnd_5975050 < baseStart_5975050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975074 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 1, 4, 2]
def baseStart_5975074 : Nat := 118140960795 + 5975074 * 2 ^ 59
def prefixEnd_5975074 : Nat := 4983230072969 + 3 ^ 40 * 5975074 * 2
def baseEnd_5975074 : Nat := 3068084908182660729196141

theorem tailTrace_5975074 : CollatzResearch.WordTrace tailWord_5975074 prefixEnd_5975074 3068084908182660729196141 := by
  unfold tailWord_5975074
  simp only [CollatzResearch.WordTrace]
  refine ⟨54482213088833708560307069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145285901570223222827485517 54482213088833708560307069)
  ·
    refine ⟨20430829908312640710115151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54482213088833708560307069 20430829908312640710115151)
    ·
      refine ⟨30646244862468961065172727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20430829908312640710115151 30646244862468961065172727)
      ·
        refine ⟨45969367293703441597759091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30646244862468961065172727 45969367293703441597759091)
        ·
          refine ⟨68954050940555162396638637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45969367293703441597759091 68954050940555162396638637)
          ·
            refine ⟨25857769102708185898739489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68954050940555162396638637 25857769102708185898739489)
            ·
              refine ⟨19393326827031139424054617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25857769102708185898739489 19393326827031139424054617)
              ·
                refine ⟨14544995120273354568040963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19393326827031139424054617 14544995120273354568040963)
                ·
                  refine ⟨21817492680410031852061445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14544995120273354568040963 21817492680410031852061445)
                  ·
                    refine ⟨4090779877576880972261521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21817492680410031852061445 4090779877576880972261521)
                    ·
                      refine ⟨3068084908182660729196141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4090779877576880972261521 3068084908182660729196141)
                      ·
                        rfl

theorem cell23_5975074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_5975074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975074 prefixEnd_5975074 := by exact prefixLift 5975074
  have htrace : WordTrace (prefixWord ++ tailWord_5975074) baseStart_5975074 baseEnd_5975074 := by
    simpa [prefixWord, tailWord_5975074, baseEnd_5975074] using wordTrace_append hprefix tailTrace_5975074
  have hstable : (prefixWord ++ tailWord_5975074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975074).length < 2 ^ (prefixWord ++ tailWord_5975074).sum := by decide
  have hdescent : baseEnd_5975074 < baseStart_5975074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975097 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 7]
def baseStart_5975097 : Nat := 118140960795 + 5975097 * 2 ^ 59
def prefixEnd_5975097 : Nat := 4983230072969 + 3 ^ 40 * 5975097 * 2
def baseEnd_5975097 : Nat := 340899635359746015467615

theorem tailTrace_5975097 : CollatzResearch.WordTrace tailWord_5975097 prefixEnd_5975097 340899635359746015467615 := by
  unfold tailWord_5975097
  simp only [CollatzResearch.WordTrace]
  refine ⟨217929691234251509169315545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145286460822834339446210363 217929691234251509169315545)
  ·
    refine ⟨163447268425688631876986659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217929691234251509169315545 163447268425688631876986659)
    ·
      refine ⟨245170902638532947815479989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163447268425688631876986659 245170902638532947815479989)
      ·
        refine ⟨22984772122362463857701249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 245170902638532947815479989 22984772122362463857701249)
        ·
          refine ⟨17238579091771847893275937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22984772122362463857701249 17238579091771847893275937)
          ·
            refine ⟨12928934318828885919956953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17238579091771847893275937 12928934318828885919956953)
            ·
              refine ⟨9696700739121664439967715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12928934318828885919956953 9696700739121664439967715)
              ·
                refine ⟨14545051108682496659951573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9696700739121664439967715 14545051108682496659951573)
                ·
                  refine ⟨340899635359746015467615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14545051108682496659951573 340899635359746015467615)
                  ·
                    rfl

theorem cell23_5975097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 7].length) (baseStart_5975097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975097 prefixEnd_5975097 := by exact prefixLift 5975097
  have htrace : WordTrace (prefixWord ++ tailWord_5975097) baseStart_5975097 baseEnd_5975097 := by
    simpa [prefixWord, tailWord_5975097, baseEnd_5975097] using wordTrace_append hprefix tailTrace_5975097
  have hstable : (prefixWord ++ tailWord_5975097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975097).length < 2 ^ (prefixWord ++ tailWord_5975097).sum := by decide
  have hdescent : baseEnd_5975097 < baseStart_5975097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975160 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 2, 1, 6]
def baseStart_5975160 : Nat := 118140960795 + 5975160 * 2 ^ 59
def prefixEnd_5975160 : Nat := 4983230072969 + 3 ^ 40 * 5975160 * 2
def baseEnd_5975160 : Nat := 3068129067518947392720745

theorem tailTrace_5975160 : CollatzResearch.WordTrace tailWord_5975160 prefixEnd_5975160 3068129067518947392720745 := by
  unfold tailWord_5975160
  simp only [CollatzResearch.WordTrace]
  refine ⟨108965994516511635464429467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145287992688682180619239289 108965994516511635464429467)
  ·
    refine ⟨163448991774767453196644201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108965994516511635464429467 163448991774767453196644201)
    ·
      refine ⟨122586743831075589897483151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163448991774767453196644201 122586743831075589897483151)
      ·
        refine ⟨183880115746613384846224727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122586743831075589897483151 183880115746613384846224727)
        ·
          refine ⟨275820173619920077269337091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183880115746613384846224727 275820173619920077269337091)
          ·
            refine ⟨413730260429880115904005637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275820173619920077269337091 413730260429880115904005637)
            ·
              refine ⟨77574423830602521732001057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 413730260429880115904005637 77574423830602521732001057)
              ·
                refine ⟨58180817872951891299000793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77574423830602521732001057 58180817872951891299000793)
                ·
                  refine ⟨43635613404713918474250595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58180817872951891299000793 43635613404713918474250595)
                  ·
                    refine ⟨65453420107070877711375893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43635613404713918474250595 65453420107070877711375893)
                    ·
                      refine ⟨3068129067518947392720745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65453420107070877711375893 3068129067518947392720745)
                      ·
                        rfl

theorem cell23_5975160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_5975160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975160 prefixEnd_5975160 := by exact prefixLift 5975160
  have htrace : WordTrace (prefixWord ++ tailWord_5975160) baseStart_5975160 baseEnd_5975160 := by
    simpa [prefixWord, tailWord_5975160, baseEnd_5975160] using wordTrace_append hprefix tailTrace_5975160
  have hstable : (prefixWord ++ tailWord_5975160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975160).length < 2 ^ (prefixWord ++ tailWord_5975160).sum := by decide
  have hdescent : baseEnd_5975160 < baseStart_5975160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975204 : List Nat := [2, 3, 1, 2, 3, 2, 2, 2, 6]
def baseStart_5975204 : Nat := 118140960795 + 5975204 * 2 ^ 59
def prefixEnd_5975204 : Nat := 4983230072969 + 3 ^ 40 * 5975204 * 2
def baseEnd_5975204 : Nat := 340905740074193913396727

theorem tailTrace_5975204 : CollatzResearch.WordTrace tailWord_5975204 prefixEnd_5975204 340905740074193913396727 := by
  unfold tailWord_5975204
  simp only [CollatzResearch.WordTrace]
  refine ⟨108966796922431933221730333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145289062563242577628973777 108966796922431933221730333)
  ·
    refine ⟨40862548845911974958148875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108966796922431933221730333 40862548845911974958148875)
    ·
      refine ⟨61293823268867962437223313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40862548845911974958148875 61293823268867962437223313)
      ·
        refine ⟨45970367451650971827917485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61293823268867962437223313 45970367451650971827917485)
        ·
          refine ⟨17238887794369114435469057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45970367451650971827917485 17238887794369114435469057)
          ·
            refine ⟨12929165845776835826601793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17238887794369114435469057 12929165845776835826601793)
            ·
              refine ⟨9696874384332626869951345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12929165845776835826601793 9696874384332626869951345)
              ·
                refine ⟨7272655788249470152463509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9696874384332626869951345 7272655788249470152463509)
                ·
                  refine ⟨340905740074193913396727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7272655788249470152463509 340905740074193913396727)
                  ·
                    rfl

theorem cell23_5975204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_5975204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975204 prefixEnd_5975204 := by exact prefixLift 5975204
  have htrace : WordTrace (prefixWord ++ tailWord_5975204) baseStart_5975204 baseEnd_5975204 := by
    simpa [prefixWord, tailWord_5975204, baseEnd_5975204] using wordTrace_append hprefix tailTrace_5975204
  have hstable : (prefixWord ++ tailWord_5975204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975204).length < 2 ^ (prefixWord ++ tailWord_5975204).sum := by decide
  have hdescent : baseEnd_5975204 < baseStart_5975204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975257 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 1, 1, 5]
def baseStart_5975257 : Nat := 118140960795 + 5975257 * 2 ^ 59
def prefixEnd_5975257 : Nat := 4983230072969 + 3 ^ 40 * 5975257 * 2
def baseEnd_5975257 : Nat := 3068178875142433513207799

theorem tailTrace_5975257 : CollatzResearch.WordTrace tailWord_5975257 prefixEnd_5975257 3068178875142433513207799 := by
  unfold tailWord_5975257
  simp only [CollatzResearch.WordTrace]
  refine ⟨217935526913671856495140025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145290351275781237663426683 217935526913671856495140025)
  ·
    refine ⟨163451645185253892371355019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217935526913671856495140025 163451645185253892371355019)
    ·
      refine ⟨245177467777880838557032529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163451645185253892371355019 245177467777880838557032529)
      ·
        refine ⟨183883100833410628917774397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245177467777880838557032529 183883100833410628917774397)
        ·
          refine ⟨68956162812528985844165399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183883100833410628917774397 68956162812528985844165399)
          ·
            refine ⟨103434244218793478766248099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68956162812528985844165399 103434244218793478766248099)
            ·
              refine ⟨155151366328190218149372149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103434244218793478766248099 155151366328190218149372149)
              ·
                refine ⟨14545440593267832951503639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 155151366328190218149372149 14545440593267832951503639)
                ·
                  refine ⟨21818160889901749427255459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14545440593267832951503639 21818160889901749427255459)
                  ·
                    refine ⟨32727241334852624140883189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21818160889901749427255459 32727241334852624140883189)
                    ·
                      refine ⟨3068178875142433513207799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32727241334852624140883189 3068178875142433513207799)
                      ·
                        rfl

theorem cell23_5975257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_5975257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975257 prefixEnd_5975257 := by exact prefixLift 5975257
  have htrace : WordTrace (prefixWord ++ tailWord_5975257) baseStart_5975257 baseEnd_5975257 := by
    simpa [prefixWord, tailWord_5975257, baseEnd_5975257] using wordTrace_append hprefix tailTrace_5975257
  have hstable : (prefixWord ++ tailWord_5975257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975257).length < 2 ^ (prefixWord ++ tailWord_5975257).sum := by decide
  have hdescent : baseEnd_5975257 < baseStart_5975257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975264 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 4, 4]
def baseStart_5975264 : Nat := 118140960795 + 5975264 * 2 ^ 59
def prefixEnd_5975264 : Nat := 4983230072969 + 3 ^ 40 * 5975264 * 2
def baseEnd_5975264 : Nat := 1022727489835671661940089

theorem tailTrace_5975264 : CollatzResearch.WordTrace tailWord_5975264 prefixEnd_5975264 1022727489835671661940089 := by
  unfold tailWord_5975264
  simp only [CollatzResearch.WordTrace]
  refine ⟨108967891112323248345322423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145290521483097664460429897 108967891112323248345322423)
  ·
    refine ⟨163451836668484872517983635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108967891112323248345322423 163451836668484872517983635)
    ·
      refine ⟨245177755002727308776975453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163451836668484872517983635 245177755002727308776975453)
      ·
        refine ⟨91941658126022740791365795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245177755002727308776975453 91941658126022740791365795)
        ·
          refine ⟨137912487189034111187048693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91941658126022740791365795 137912487189034111187048693)
          ·
            refine ⟨12929295673971947923785815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137912487189034111187048693 12929295673971947923785815)
            ·
              refine ⟨19393943510957921885678723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12929295673971947923785815 19393943510957921885678723)
              ·
                refine ⟨29090915266436882828518085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19393943510957921885678723 29090915266436882828518085)
                ·
                  refine ⟨5454546612456915530347141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29090915266436882828518085 5454546612456915530347141)
                  ·
                    refine ⟨1022727489835671661940089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5454546612456915530347141 1022727489835671661940089)
                    ·
                      rfl

theorem cell23_5975264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 4, 4].length) (baseStart_5975264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975264 prefixEnd_5975264 := by exact prefixLift 5975264
  have htrace : WordTrace (prefixWord ++ tailWord_5975264) baseStart_5975264 baseEnd_5975264 := by
    simpa [prefixWord, tailWord_5975264, baseEnd_5975264] using wordTrace_append hprefix tailTrace_5975264
  have hstable : (prefixWord ++ tailWord_5975264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975264).length < 2 ^ (prefixWord ++ tailWord_5975264).sum := by decide
  have hdescent : baseEnd_5975264 < baseStart_5975264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975274 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_5975274 : Nat := 118140960795 + 5975274 * 2 ^ 59
def prefixEnd_5975274 : Nat := 4983230072969 + 3 ^ 40 * 5975274 * 2
def baseEnd_5975274 : Nat := 3068187604313559946695221

theorem tailTrace_5975274 : CollatzResearch.WordTrace tailWord_5975274 prefixEnd_5975274 3068187604313559946695221 := by
  unfold tailWord_5975274
  simp only [CollatzResearch.WordTrace]
  refine ⟨54484036738652567099627219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145290764636406845599005917 54484036738652567099627219)
  ·
    refine ⟨81726055107978850649440829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54484036738652567099627219 81726055107978850649440829)
    ·
      refine ⟨30647270665492068993540311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81726055107978850649440829 30647270665492068993540311)
      ·
        refine ⟨45970905998238103490310467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30647270665492068993540311 45970905998238103490310467)
        ·
          refine ⟨68956358997357155235465701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45970905998238103490310467 68956358997357155235465701)
          ·
            refine ⟨12929317312004466606649819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68956358997357155235465701 12929317312004466606649819)
            ·
              refine ⟨19393975968006699909974729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12929317312004466606649819 19393975968006699909974729)
              ·
                refine ⟨14545481976005024932481047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19393975968006699909974729 14545481976005024932481047)
                ·
                  refine ⟨21818222964007537398721571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14545481976005024932481047 21818222964007537398721571)
                  ·
                    refine ⟨32727334446011306098082357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21818222964007537398721571 32727334446011306098082357)
                    ·
                      refine ⟨3068187604313559946695221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32727334446011306098082357 3068187604313559946695221)
                      ·
                        rfl

theorem cell23_5975274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_5975274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975274 prefixEnd_5975274 := by exact prefixLift 5975274
  have htrace : WordTrace (prefixWord ++ tailWord_5975274) baseStart_5975274 baseEnd_5975274 := by
    simpa [prefixWord, tailWord_5975274, baseEnd_5975274] using wordTrace_append hprefix tailTrace_5975274
  have hstable : (prefixWord ++ tailWord_5975274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975274).length < 2 ^ (prefixWord ++ tailWord_5975274).sum := by decide
  have hdescent : baseEnd_5975274 < baseStart_5975274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975294 : List Nat := [4, 2, 2, 1, 1, 3, 1, 9]
def baseStart_5975294 : Nat := 118140960795 + 5975294 * 2 ^ 59
def prefixEnd_5975294 : Nat := 4983230072969 + 3 ^ 40 * 5975294 * 2
def baseEnd_5975294 : Nat := 113636958293579624757227

theorem tailTrace_5975294 : CollatzResearch.WordTrace tailWord_5975294 prefixEnd_5975294 113636958293579624757227 := by
  unfold tailWord_5975294
  simp only [CollatzResearch.WordTrace]
  refine ⟨27242109551817226476779617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145291250943025207876157957 27242109551817226476779617)
  ·
    refine ⟨20431582163862919857584713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27242109551817226476779617 20431582163862919857584713)
    ·
      refine ⟨15323686622897189893188535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20431582163862919857584713 15323686622897189893188535)
      ·
        refine ⟨22985529934345784839782803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15323686622897189893188535 22985529934345784839782803)
        ·
          refine ⟨34478294901518677259674205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22985529934345784839782803 34478294901518677259674205)
          ·
            refine ⟨12929360588069503972377827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34478294901518677259674205 12929360588069503972377827)
            ·
              refine ⟨19394040882104255958566741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12929360588069503972377827 19394040882104255958566741)
              ·
                refine ⟨113636958293579624757227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19394040882104255958566741 113636958293579624757227)
                ·
                  rfl

theorem cell23_5975294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 9].length) (baseStart_5975294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975294 prefixEnd_5975294 := by exact prefixLift 5975294
  have htrace : WordTrace (prefixWord ++ tailWord_5975294) baseStart_5975294 baseEnd_5975294 := by
    simpa [prefixWord, tailWord_5975294, baseEnd_5975294] using wordTrace_append hprefix tailTrace_5975294
  have hstable : (prefixWord ++ tailWord_5975294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975294).length < 2 ^ (prefixWord ++ tailWord_5975294).sum := by decide
  have hdescent : baseEnd_5975294 < baseStart_5975294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975317 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_5975317 : Nat := 118140960795 + 5975317 * 2 ^ 59
def prefixEnd_5975317 : Nat := 4983230072969 + 3 ^ 40 * 5975317 * 2
def baseEnd_5975317 : Nat := 3068209683981703278457523

theorem tailTrace_5975317 : CollatzResearch.WordTrace tailWord_5975317 prefixEnd_5975317 3068209683981703278457523 := by
  unfold tailWord_5975317
  simp only [CollatzResearch.WordTrace]
  refine ⟨217937715293454486742324205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145291810195636324494882803 217937715293454486742324205)
  ·
    refine ⟨81726643235045432528371577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217937715293454486742324205 81726643235045432528371577)
    ·
      refine ⟨61294982426284074396278683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81726643235045432528371577 61294982426284074396278683)
      ·
        refine ⟨91942473639426111594418025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61294982426284074396278683 91942473639426111594418025)
        ·
          refine ⟨68956855229569583695813519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91942473639426111594418025 68956855229569583695813519)
          ·
            refine ⟨103435282844354375543720279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68956855229569583695813519 103435282844354375543720279)
            ·
              refine ⟨155152924266531563315580419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103435282844354375543720279 155152924266531563315580419)
              ·
                refine ⟨232729386399797344973370629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155152924266531563315580419 232729386399797344973370629)
                ·
                  refine ⟨43636759949962002182506993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 232729386399797344973370629 43636759949962002182506993)
                  ·
                    refine ⟨32727569962471501636880245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43636759949962002182506993 32727569962471501636880245)
                    ·
                      refine ⟨3068209683981703278457523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32727569962471501636880245 3068209683981703278457523)
                      ·
                        rfl

theorem cell23_5975317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_5975317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975317 prefixEnd_5975317 := by exact prefixLift 5975317
  have htrace : WordTrace (prefixWord ++ tailWord_5975317) baseStart_5975317 baseEnd_5975317 := by
    simpa [prefixWord, tailWord_5975317, baseEnd_5975317] using wordTrace_append hprefix tailTrace_5975317
  have hstable : (prefixWord ++ tailWord_5975317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975317).length < 2 ^ (prefixWord ++ tailWord_5975317).sum := by decide
  have hdescent : baseEnd_5975317 < baseStart_5975317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975322 : List Nat := [3, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2]
def baseStart_5975322 : Nat := 118140960795 + 5975322 * 2 ^ 59
def prefixEnd_5975322 : Nat := 4983230072969 + 3 ^ 40 * 5975322 * 2
def baseEnd_5975322 : Nat := 3068212251384975758895001

theorem tailTrace_5975322 : CollatzResearch.WordTrace tailWord_5975322 prefixEnd_5975322 3068212251384975758895001 := by
  unfold tailWord_5975322
  simp only [CollatzResearch.WordTrace]
  refine ⟨54484474414609093149064055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145291931772290915064170813 54484474414609093149064055)
  ·
    refine ⟨81726711621913639723596083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54484474414609093149064055 81726711621913639723596083)
    ·
      refine ⟨122590067432870459585394125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81726711621913639723596083 122590067432870459585394125)
      ·
        refine ⟨45971275287326422344522797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122590067432870459585394125 45971275287326422344522797)
        ·
          refine ⟨17239228232747408379196049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45971275287326422344522797 17239228232747408379196049)
          ·
            refine ⟨12929421174560556284397037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17239228232747408379196049 12929421174560556284397037)
            ·
              refine ⟨4848532940460208606648889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12929421174560556284397037 4848532940460208606648889)
              ·
                refine ⟨3636399705345156454986667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4848532940460208606648889 3636399705345156454986667)
                ·
                  refine ⟨5454599558017734682480001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3636399705345156454986667 5454599558017734682480001)
                  ·
                    refine ⟨4090949668513301011860001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5454599558017734682480001 4090949668513301011860001)
                    ·
                      refine ⟨3068212251384975758895001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4090949668513301011860001 3068212251384975758895001)
                      ·
                        rfl

theorem cell23_5975322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_5975322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975322 prefixEnd_5975322 := by exact prefixLift 5975322
  have htrace : WordTrace (prefixWord ++ tailWord_5975322) baseStart_5975322 baseEnd_5975322 := by
    simpa [prefixWord, tailWord_5975322, baseEnd_5975322] using wordTrace_append hprefix tailTrace_5975322
  have hstable : (prefixWord ++ tailWord_5975322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975322).length < 2 ^ (prefixWord ++ tailWord_5975322).sum := by decide
  have hdescent : baseEnd_5975322 < baseStart_5975322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975348 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_5975348 : Nat := 118140960795 + 5975348 * 2 ^ 59
def prefixEnd_5975348 : Nat := 4983230072969 + 3 ^ 40 * 5975348 * 2
def baseEnd_5975348 : Nat := 3068225601881992657169881

theorem tailTrace_5975348 : CollatzResearch.WordTrace tailWord_5975348 prefixEnd_5975348 3068225601881992657169881 := by
  unfold tailWord_5975348
  simp only [CollatzResearch.WordTrace]
  refine ⟨108969422978171089518351349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145292563970894786024468465 108969422978171089518351349)
  ·
    refine ⟨10215883404203539642345439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108969422978171089518351349 10215883404203539642345439)
    ·
      refine ⟨15323825106305309463518159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10215883404203539642345439 15323825106305309463518159)
      ·
        refine ⟨22985737659457964195277239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15323825106305309463518159 22985737659457964195277239)
        ·
          refine ⟨34478606489186946292915859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22985737659457964195277239 34478606489186946292915859)
          ·
            refine ⟨51717909733780419439373789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34478606489186946292915859 51717909733780419439373789)
            ·
              refine ⟨19394216150167657289765171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51717909733780419439373789 19394216150167657289765171)
              ·
                refine ⟨29091324225251485934647757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19394216150167657289765171 29091324225251485934647757)
                ·
                  refine ⟨10909246584469307225492909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29091324225251485934647757 10909246584469307225492909)
                  ·
                    refine ⟨4090967469175990209559841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10909246584469307225492909 4090967469175990209559841)
                    ·
                      refine ⟨3068225601881992657169881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4090967469175990209559841 3068225601881992657169881)
                      ·
                        rfl

theorem cell23_5975348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_5975348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975348 prefixEnd_5975348 := by exact prefixLift 5975348
  have htrace : WordTrace (prefixWord ++ tailWord_5975348) baseStart_5975348 baseEnd_5975348 := by
    simpa [prefixWord, tailWord_5975348, baseEnd_5975348] using wordTrace_append hprefix tailTrace_5975348
  have hstable : (prefixWord ++ tailWord_5975348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975348).length < 2 ^ (prefixWord ++ tailWord_5975348).sum := by decide
  have hdescent : baseEnd_5975348 < baseStart_5975348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975373 : List Nat := [1, 6, 1, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_5975373 : Nat := 118140960795 + 5975373 * 2 ^ 59
def prefixEnd_5975373 : Nat := 4983230072969 + 3 ^ 40 * 5975373 * 2
def baseEnd_5975373 : Nat := 3068238438898355059357267

theorem tailTrace_5975373 : CollatzResearch.WordTrace tailWord_5975373 prefixEnd_5975373 3068238438898355059357267 := by
  unfold tailWord_5975373
  simp only [CollatzResearch.WordTrace]
  refine ⟨217939757781251608306362773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145293171854167738870908515 217939757781251608306362773)
  ·
    refine ⟨10215926145996169139360755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 217939757781251608306362773 10215926145996169139360755)
    ·
      refine ⟨15323889218994253709041133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10215926145996169139360755 15323889218994253709041133)
      ·
        refine ⟨5746458457122845140890425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15323889218994253709041133 5746458457122845140890425)
        ·
          refine ⟨4309843842842133855667819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5746458457122845140890425 4309843842842133855667819)
          ·
            refine ⟨6464765764263200783501729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4309843842842133855667819 6464765764263200783501729)
            ·
              refine ⟨4848574323197400587626297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6464765764263200783501729 4848574323197400587626297)
              ·
                refine ⟨3636430742398050440719723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4848574323197400587626297 3636430742398050440719723)
                ·
                  refine ⟨5454646113597075661079585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3636430742398050440719723 5454646113597075661079585)
                  ·
                    refine ⟨4090984585197806745809689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5454646113597075661079585 4090984585197806745809689)
                    ·
                      refine ⟨3068238438898355059357267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4090984585197806745809689 3068238438898355059357267)
                      ·
                        rfl

theorem cell23_5975373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_5975373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975373 prefixEnd_5975373 := by exact prefixLift 5975373
  have htrace : WordTrace (prefixWord ++ tailWord_5975373) baseStart_5975373 baseEnd_5975373 := by
    simpa [prefixWord, tailWord_5975373, baseEnd_5975373] using wordTrace_append hprefix tailTrace_5975373
  have hstable : (prefixWord ++ tailWord_5975373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975373).length < 2 ^ (prefixWord ++ tailWord_5975373).sum := by decide
  have hdescent : baseEnd_5975373 < baseStart_5975373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975374 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_5975374 : Nat := 118140960795 + 5975374 * 2 ^ 59
def prefixEnd_5975374 : Nat := 4983230072969 + 3 ^ 40 * 5975374 * 2
def baseEnd_5975374 : Nat := 3068238952379009555444761

theorem tailTrace_5975374 : CollatzResearch.WordTrace tailWord_5975374 prefixEnd_5975374 3068238952379009555444761 := by
  unfold tailWord_5975374
  simp only [CollatzResearch.WordTrace]
  refine ⟨27242474281780998184643647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145293196169498656984766117 27242474281780998184643647)
  ·
    refine ⟨40863711422671497276965471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27242474281780998184643647 40863711422671497276965471)
    ·
      refine ⟨61295567134007245915448207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40863711422671497276965471 61295567134007245915448207)
      ·
        refine ⟨91943350701010868873172311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61295567134007245915448207 91943350701010868873172311)
        ·
          refine ⟨137915026051516303309758467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91943350701010868873172311 137915026051516303309758467)
          ·
            refine ⟨206872539077274454964637701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137915026051516303309758467 206872539077274454964637701)
            ·
              refine ⟨38788601076988960305869569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206872539077274454964637701 38788601076988960305869569)
              ·
                refine ⟨29091450807741720229402177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38788601076988960305869569 29091450807741720229402177)
                ·
                  refine ⟨21818588105806290172051633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29091450807741720229402177 21818588105806290172051633)
                  ·
                    refine ⟨16363941079354717629038725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21818588105806290172051633 16363941079354717629038725)
                    ·
                      refine ⟨3068238952379009555444761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16363941079354717629038725 3068238952379009555444761)
                      ·
                        rfl

theorem cell23_5975374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_5975374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975374 prefixEnd_5975374 := by exact prefixLift 5975374
  have htrace : WordTrace (prefixWord ++ tailWord_5975374) baseStart_5975374 baseEnd_5975374 := by
    simpa [prefixWord, tailWord_5975374, baseEnd_5975374] using wordTrace_append hprefix tailTrace_5975374
  have hstable : (prefixWord ++ tailWord_5975374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975374).length < 2 ^ (prefixWord ++ tailWord_5975374).sum := by decide
  have hdescent : baseEnd_5975374 < baseStart_5975374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975495 : List Nat := [1, 1, 4, 1, 1, 3, 5, 2, 1, 4]
def baseStart_5975495 : Nat := 118140960795 + 5975495 * 2 ^ 59
def prefixEnd_5975495 : Nat := 4983230072969 + 3 ^ 40 * 5975495 * 2
def baseEnd_5975495 : Nat := 1022767027846067860677235

theorem tailTrace_5975495 : CollatzResearch.WordTrace tailWord_5975495 prefixEnd_5975495 1022767027846067860677235 := by
  unfold tailWord_5975495
  simp only [CollatzResearch.WordTrace]
  refine ⟨217944207486809623142303939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145296138324539748761535959 217944207486809623142303939)
  ·
    refine ⟨326916311230214434713455909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217944207486809623142303939 326916311230214434713455909)
    ·
      refine ⟨61296808355665206508772983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326916311230214434713455909 61296808355665206508772983)
      ·
        refine ⟨91945212533497809763159475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61296808355665206508772983 91945212533497809763159475)
        ·
          refine ⟨137917818800246714644739213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91945212533497809763159475 137917818800246714644739213)
          ·
            refine ⟨51719182050092517991777205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137917818800246714644739213 51719182050092517991777205)
            ·
              refine ⟨4848673317196173561729113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51719182050092517991777205 4848673317196173561729113)
              ·
                refine ⟨3636504987897130171296835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4848673317196173561729113 3636504987897130171296835)
                ·
                  refine ⟨5454757481845695256945253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3636504987897130171296835 5454757481845695256945253)
                  ·
                    refine ⟨1022767027846067860677235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5454757481845695256945253 1022767027846067860677235)
                    ·
                      rfl

theorem cell23_5975495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_5975495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975495 prefixEnd_5975495 := by exact prefixLift 5975495
  have htrace : WordTrace (prefixWord ++ tailWord_5975495) baseStart_5975495 baseEnd_5975495 := by
    simpa [prefixWord, tailWord_5975495, baseEnd_5975495] using wordTrace_append hprefix tailTrace_5975495
  have hstable : (prefixWord ++ tailWord_5975495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975495).length < 2 ^ (prefixWord ++ tailWord_5975495).sum := by decide
  have hdescent : baseEnd_5975495 < baseStart_5975495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975504 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 5, 5]
def baseStart_5975504 : Nat := 118140960795 + 5975504 * 2 ^ 59
def prefixEnd_5975504 : Nat := 4983230072969 + 3 ^ 40 * 5975504 * 2
def baseEnd_5975504 : Nat := 1022768568288031348939721

theorem tailTrace_5975504 : CollatzResearch.WordTrace tailWord_5975504 prefixEnd_5975504 1022768568288031348939721 := by
  unfold tailWord_5975504
  simp only [CollatzResearch.WordTrace]
  refine ⟨108972267871888508839690783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145296357162518011786254377 108972267871888508839690783)
  ·
    refine ⟨163458401807832763259536175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108972267871888508839690783 163458401807832763259536175)
    ·
      refine ⟨245187602711749144889304263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163458401807832763259536175 245187602711749144889304263)
      ·
        refine ⟨367781404067623717333956395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245187602711749144889304263 367781404067623717333956395)
        ·
          refine ⟨551672106101435576000934593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367781404067623717333956395 551672106101435576000934593)
          ·
            refine ⟨413754079576076682000700945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551672106101435576000934593 413754079576076682000700945)
            ·
              refine ⟨310315559682057511500525709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413754079576076682000700945 310315559682057511500525709)
              ·
                refine ⟨116368334880771566812697141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310315559682057511500525709 116368334880771566812697141)
                ·
                  refine ⟨10909531395072334388690357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116368334880771566812697141 10909531395072334388690357)
                  ·
                    refine ⟨1022768568288031348939721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10909531395072334388690357 1022768568288031348939721)
                    ·
                      rfl

theorem cell23_5975504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 5, 5].length) (baseStart_5975504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975504 prefixEnd_5975504 := by exact prefixLift 5975504
  have htrace : WordTrace (prefixWord ++ tailWord_5975504) baseStart_5975504 baseEnd_5975504 := by
    simpa [prefixWord, tailWord_5975504, baseEnd_5975504] using wordTrace_append hprefix tailTrace_5975504
  have hstable : (prefixWord ++ tailWord_5975504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975504).length < 2 ^ (prefixWord ++ tailWord_5975504).sum := by decide
  have hdescent : baseEnd_5975504 < baseStart_5975504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975508 : List Nat := [2, 4, 1, 2, 3, 1, 1, 3, 6]
def baseStart_5975508 : Nat := 118140960795 + 5975508 * 2 ^ 59
def prefixEnd_5975508 : Nat := 4983230072969 + 3 ^ 40 * 5975508 * 2
def baseEnd_5975508 : Nat := 340923084309634670129905

theorem tailTrace_5975508 : CollatzResearch.WordTrace tailWord_5975508 prefixEnd_5975508 340923084309634670129905 := by
  unfold tailWord_5975508
  simp only [CollatzResearch.WordTrace]
  refine ⟨108972340817881263181263589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145296454423841684241684785 108972340817881263181263589)
  ·
    refine ⟨20432313903352736846486923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108972340817881263181263589 20432313903352736846486923)
    ·
      refine ⟨30648470855029105269730385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20432313903352736846486923 30648470855029105269730385)
      ·
        refine ⟨22986353141271828952297789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30648470855029105269730385 22986353141271828952297789)
        ·
          refine ⟨8619882427976935857111671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22986353141271828952297789 8619882427976935857111671)
          ·
            refine ⟨12929823641965403785667507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8619882427976935857111671 12929823641965403785667507)
            ·
              refine ⟨19394735462948105678501261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12929823641965403785667507 19394735462948105678501261)
              ·
                refine ⟨7273025798605539629437973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19394735462948105678501261 7273025798605539629437973)
                ·
                  refine ⟨340923084309634670129905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7273025798605539629437973 340923084309634670129905)
                  ·
                    rfl

theorem cell23_5975508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_5975508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975508 prefixEnd_5975508 := by exact prefixLift 5975508
  have htrace : WordTrace (prefixWord ++ tailWord_5975508) baseStart_5975508 baseEnd_5975508 := by
    simpa [prefixWord, tailWord_5975508, baseEnd_5975508] using wordTrace_append hprefix tailTrace_5975508
  have hstable : (prefixWord ++ tailWord_5975508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975508).length < 2 ^ (prefixWord ++ tailWord_5975508).sum := by decide
  have hdescent : baseEnd_5975508 < baseStart_5975508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975511 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 3, 5, 2]
def baseStart_5975511 : Nat := 118140960795 + 5975511 * 2 ^ 59
def prefixEnd_5975511 : Nat := 4983230072969 + 3 ^ 40 * 5975511 * 2
def baseEnd_5975511 : Nat := 3068309299228675519431631

theorem tailTrace_5975511 : CollatzResearch.WordTrace tailWord_5975511 prefixEnd_5975511 3068309299228675519431631 := by
  unfold tailWord_5975511
  simp only [CollatzResearch.WordTrace]
  refine ⟨217944791054751657874886387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145296527369834438583257591 217944791054751657874886387)
  ·
    refine ⟨326917186582127486812329581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217944791054751657874886387 326917186582127486812329581)
    ·
      refine ⟨122593944968297807554623593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326917186582127486812329581 122593944968297807554623593)
      ·
        refine ⟨91945458726223355665967695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122593944968297807554623593 91945458726223355665967695)
        ·
          refine ⟨137918188089335033498951543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91945458726223355665967695 137918188089335033498951543)
          ·
            refine ⟨206877282134002550248427315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137918188089335033498951543 206877282134002550248427315)
            ·
              refine ⟨310315923201003825372640973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206877282134002550248427315 310315923201003825372640973)
              ·
                refine ⟨116368471200376434514740365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310315923201003825372640973 116368471200376434514740365)
                ·
                  refine ⟨43638176700141162943027637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116368471200376434514740365 43638176700141162943027637)
                  ·
                    refine ⟨4091079065638234025908841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43638176700141162943027637 4091079065638234025908841)
                    ·
                      refine ⟨3068309299228675519431631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4091079065638234025908841 3068309299228675519431631)
                      ·
                        rfl

theorem cell23_5975511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_5975511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975511 prefixEnd_5975511 := by exact prefixLift 5975511
  have htrace : WordTrace (prefixWord ++ tailWord_5975511) baseStart_5975511 baseEnd_5975511 := by
    simpa [prefixWord, tailWord_5975511, baseEnd_5975511] using wordTrace_append hprefix tailTrace_5975511
  have hstable : (prefixWord ++ tailWord_5975511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975511).length < 2 ^ (prefixWord ++ tailWord_5975511).sum := by decide
  have hdescent : baseEnd_5975511 < baseStart_5975511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975521 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 3, 5]
def baseStart_5975521 : Nat := 118140960795 + 5975521 * 2 ^ 59
def prefixEnd_5975521 : Nat := 4983230072969 + 3 ^ 40 * 5975521 * 2
def baseEnd_5975521 : Nat := 1022771478011740160102195

theorem tailTrace_5975521 : CollatzResearch.WordTrace tailWord_5975521 prefixEnd_5975521 1022771478011740160102195 := by
  unfold tailWord_5975521
  simp only [CollatzResearch.WordTrace]
  refine ⟨217945155784715429582750417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145296770523143619721833611 217945155784715429582750417)
  ·
    refine ⟨163458866838536572187062813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217945155784715429582750417 163458866838536572187062813)
    ·
      refine ⟨61297075064451214570148555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163458866838536572187062813 61297075064451214570148555)
      ·
        refine ⟨91945612596676821855222833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61297075064451214570148555 91945612596676821855222833)
        ·
          refine ⟨68959209447507616391417125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91945612596676821855222833 68959209447507616391417125)
          ·
            refine ⟨12929851771407678073390711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68959209447507616391417125 12929851771407678073390711)
            ·
              refine ⟨19394777657111517110086067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12929851771407678073390711 19394777657111517110086067)
              ·
                refine ⟨29092166485667275665129101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19394777657111517110086067 29092166485667275665129101)
                ·
                  refine ⟨10909562432125228374423413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29092166485667275665129101 10909562432125228374423413)
                  ·
                    refine ⟨1022771478011740160102195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10909562432125228374423413 1022771478011740160102195)
                    ·
                      rfl

theorem cell23_5975521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_5975521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975521 prefixEnd_5975521 := by exact prefixLift 5975521
  have htrace : WordTrace (prefixWord ++ tailWord_5975521) baseStart_5975521 baseEnd_5975521 := by
    simpa [prefixWord, tailWord_5975521, baseEnd_5975521] using wordTrace_append hprefix tailTrace_5975521
  have hstable : (prefixWord ++ tailWord_5975521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975521).length < 2 ^ (prefixWord ++ tailWord_5975521).sum := by decide
  have hdescent : baseEnd_5975521 < baseStart_5975521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975561 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 5, 2, 3]
def baseStart_5975561 : Nat := 118140960795 + 5975561 * 2 ^ 59
def prefixEnd_5975561 : Nat := 4983230072969 + 3 ^ 40 * 5975561 * 2
def baseEnd_5975561 : Nat := 3068334973261400323806401

theorem tailTrace_5975561 : CollatzResearch.WordTrace tailWord_5975561 prefixEnd_5975561 3068334973261400323806401 := by
  unfold tailWord_5975561
  simp only [CollatzResearch.WordTrace]
  refine ⟨217946614704570516414206537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145297743136380344276137691 217946614704570516414206537)
  ·
    refine ⟨163459961028427887310654903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217946614704570516414206537 163459961028427887310654903)
    ·
      refine ⟨245189941542641830965982355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163459961028427887310654903 245189941542641830965982355)
      ·
        refine ⟨367784912313962746448973533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245189941542641830965982355 367784912313962746448973533)
        ·
          refine ⟨137919342117736029918365075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367784912313962746448973533 137919342117736029918365075)
          ·
            refine ⟨206879013176604044877547613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137919342117736029918365075 206879013176604044877547613)
            ·
              refine ⟨77579629941226516829080355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206879013176604044877547613 77579629941226516829080355)
              ·
                refine ⟨116369444911839775243620533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77579629941226516829080355 116369444911839775243620533)
                ·
                  refine ⟨10909635460484978929089425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116369444911839775243620533 10909635460484978929089425)
                  ·
                    refine ⟨8182226595363734196817069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10909635460484978929089425 8182226595363734196817069)
                    ·
                      refine ⟨3068334973261400323806401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8182226595363734196817069 3068334973261400323806401)
                      ·
                        rfl

theorem cell23_5975561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 2, 3].length) (baseStart_5975561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975561 prefixEnd_5975561 := by exact prefixLift 5975561
  have htrace : WordTrace (prefixWord ++ tailWord_5975561) baseStart_5975561 baseEnd_5975561 := by
    simpa [prefixWord, tailWord_5975561, baseEnd_5975561] using wordTrace_append hprefix tailTrace_5975561
  have hstable : (prefixWord ++ tailWord_5975561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975561).length < 2 ^ (prefixWord ++ tailWord_5975561).sum := by decide
  have hdescent : baseEnd_5975561 < baseStart_5975561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975571 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 4]
def baseStart_5975571 : Nat := 118140960795 + 5975571 * 2 ^ 59
def prefixEnd_5975571 : Nat := 4983230072969 + 3 ^ 40 * 5975571 * 2
def baseEnd_5975571 : Nat := 3068340108067945284681355

theorem tailTrace_5975571 : CollatzResearch.WordTrace tailWord_5975571 prefixEnd_5975571 3068340108067945284681355 := by
  unfold tailWord_5975571
  simp only [CollatzResearch.WordTrace]
  refine ⟨217946979434534288122070567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145297986289689525414713711 217946979434534288122070567)
  ·
    refine ⟨326920469151801432183105851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217946979434534288122070567 326920469151801432183105851)
    ·
      refine ⟨490380703727702148274658777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326920469151801432183105851 490380703727702148274658777)
      ·
        refine ⟨367785527795776611205994083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490380703727702148274658777 367785527795776611205994083)
        ·
          refine ⟨551678291693664916808991125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367785527795776611205994083 551678291693664916808991125)
          ·
            refine ⟨25859919923140542975421459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 551678291693664916808991125 25859919923140542975421459)
            ·
              refine ⟨38789879884710814463132189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25859919923140542975421459 38789879884710814463132189)
              ·
                refine ⟨14546204956766555423674571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38789879884710814463132189 14546204956766555423674571)
                ·
                  refine ⟨21819307435149833135511857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14546204956766555423674571 21819307435149833135511857)
                  ·
                    refine ⟨16364480576362374851633893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21819307435149833135511857 16364480576362374851633893)
                    ·
                      refine ⟨3068340108067945284681355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16364480576362374851633893 3068340108067945284681355)
                      ·
                        rfl

theorem cell23_5975571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 4].length) (baseStart_5975571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975571 prefixEnd_5975571 := by exact prefixLift 5975571
  have htrace : WordTrace (prefixWord ++ tailWord_5975571) baseStart_5975571 baseEnd_5975571 := by
    simpa [prefixWord, tailWord_5975571, baseEnd_5975571] using wordTrace_append hprefix tailTrace_5975571
  have hstable : (prefixWord ++ tailWord_5975571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975571).length < 2 ^ (prefixWord ++ tailWord_5975571).sum := by decide
  have hdescent : baseEnd_5975571 < baseStart_5975571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975578 : List Nat := [3, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3]
def baseStart_5975578 : Nat := 118140960795 + 5975578 * 2 ^ 59
def prefixEnd_5975578 : Nat := 4983230072969 + 3 ^ 40 * 5975578 * 2
def baseEnd_5975578 : Nat := 3068343702432526757293823

theorem tailTrace_5975578 : CollatzResearch.WordTrace tailWord_5975578 prefixEnd_5975578 3068343702432526757293823 := by
  unfold tailWord_5975578
  simp only [CollatzResearch.WordTrace]
  refine ⟨54486808686377232079393847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145298156497005952211716925 54486808686377232079393847)
  ·
    refine ⟨81730213029565848119090771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54486808686377232079393847 81730213029565848119090771)
    ·
      refine ⟨122595319544348772178636157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81730213029565848119090771 122595319544348772178636157)
      ·
        refine ⟨45973244829130789566988559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122595319544348772178636157 45973244829130789566988559)
        ·
          refine ⟨68959867243696184350482839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45973244829130789566988559 68959867243696184350482839)
          ·
            refine ⟨103439800865544276525724259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68959867243696184350482839 103439800865544276525724259)
            ·
              refine ⟨155159701298316414788586389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103439800865544276525724259 155159701298316414788586389)
              ·
                refine ⟨7273110998358581943214987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 155159701298316414788586389 7273110998358581943214987)
                ·
                  refine ⟨10909666497537872914822481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7273110998358581943214987 10909666497537872914822481)
                  ·
                    refine ⟨8182249873153404686116861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10909666497537872914822481 8182249873153404686116861)
                    ·
                      refine ⟨3068343702432526757293823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8182249873153404686116861 3068343702432526757293823)
                      ·
                        rfl

theorem cell23_5975578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_5975578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975578 prefixEnd_5975578 := by exact prefixLift 5975578
  have htrace : WordTrace (prefixWord ++ tailWord_5975578) baseStart_5975578 baseEnd_5975578 := by
    simpa [prefixWord, tailWord_5975578, baseEnd_5975578] using wordTrace_append hprefix tailTrace_5975578
  have hstable : (prefixWord ++ tailWord_5975578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975578).length < 2 ^ (prefixWord ++ tailWord_5975578).sum := by decide
  have hdescent : baseEnd_5975578 < baseStart_5975578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975648 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 3, 4, 2]
def baseStart_5975648 : Nat := 118140960795 + 5975648 * 2 ^ 59
def prefixEnd_5975648 : Nat := 4983230072969 + 3 ^ 40 * 5975648 * 2
def baseEnd_5975648 : Nat := 3068379646078341483418501

theorem tailTrace_5975648 : CollatzResearch.WordTrace tailWord_5975648 prefixEnd_5975648 3068379646078341483418501 := by
  unfold tailWord_5975648
  simp only [CollatzResearch.WordTrace]
  refine ⟨108974893927627665136311799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145299858570170220181749065 108974893927627665136311799)
  ·
    refine ⟨163462340891441497704467699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108974893927627665136311799 163462340891441497704467699)
    ·
      refine ⟨245193511337162246556701549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163462340891441497704467699 245193511337162246556701549)
      ·
        refine ⟨91947566751435842458763081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245193511337162246556701549 91947566751435842458763081)
        ·
          refine ⟨68960675063576881844072311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91947566751435842458763081 68960675063576881844072311)
          ·
            refine ⟨103441012595365322766108467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68960675063576881844072311 103441012595365322766108467)
            ·
              refine ⟨155161518893047984149162701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103441012595365322766108467 155161518893047984149162701)
              ·
                refine ⟨58185569584892994055936013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155161518893047984149162701 58185569584892994055936013)
                ·
                  refine ⟨21819588594334872770976005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58185569584892994055936013 21819588594334872770976005)
                  ·
                    refine ⟨4091172861437788644558001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21819588594334872770976005 4091172861437788644558001)
                    ·
                      refine ⟨3068379646078341483418501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4091172861437788644558001 3068379646078341483418501)
                      ·
                        rfl

theorem cell23_5975648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_5975648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975648 prefixEnd_5975648 := by exact prefixLift 5975648
  have htrace : WordTrace (prefixWord ++ tailWord_5975648) baseStart_5975648 baseEnd_5975648 := by
    simpa [prefixWord, tailWord_5975648, baseEnd_5975648] using wordTrace_append hprefix tailTrace_5975648
  have hstable : (prefixWord ++ tailWord_5975648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975648).length < 2 ^ (prefixWord ++ tailWord_5975648).sum := by decide
  have hdescent : baseEnd_5975648 < baseStart_5975648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975651 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 5]
def baseStart_5975651 : Nat := 118140960795 + 5975651 * 2 ^ 59
def prefixEnd_5975651 : Nat := 4983230072969 + 3 ^ 40 * 5975651 * 2
def baseEnd_5975651 : Nat := 3068381186520304971680987

theorem tailTrace_5975651 : CollatzResearch.WordTrace tailWord_5975651 prefixEnd_5975651 3068381186520304971680987 := by
  unfold tailWord_5975651
  simp only [CollatzResearch.WordTrace]
  refine ⟨217949897274244461784982807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145299931516162974523321871 217949897274244461784982807)
  ·
    refine ⟨326924845911366692677474211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217949897274244461784982807 326924845911366692677474211)
    ·
      refine ⟨490387268867050039016211317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326924845911366692677474211 490387268867050039016211317)
      ·
        refine ⟨45973806456285941157769811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 490387268867050039016211317 45973806456285941157769811)
        ·
          refine ⟨68960709684428911736654717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45973806456285941157769811 68960709684428911736654717)
          ·
            refine ⟨25860266131660841901245519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68960709684428911736654717 25860266131660841901245519)
            ·
              refine ⟨38790399197491262851868279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25860266131660841901245519 38790399197491262851868279)
              ·
                refine ⟨58185598796236894277802419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38790399197491262851868279 58185598796236894277802419)
                ·
                  refine ⟨87278398194355341416703629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58185598796236894277802419 87278398194355341416703629)
                  ·
                    refine ⟨32729399322883253031263861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87278398194355341416703629 32729399322883253031263861)
                    ·
                      refine ⟨3068381186520304971680987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32729399322883253031263861 3068381186520304971680987)
                      ·
                        rfl

theorem cell23_5975651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_5975651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975651 prefixEnd_5975651 := by exact prefixLift 5975651
  have htrace : WordTrace (prefixWord ++ tailWord_5975651) baseStart_5975651 baseEnd_5975651 := by
    simpa [prefixWord, tailWord_5975651, baseEnd_5975651] using wordTrace_append hprefix tailTrace_5975651
  have hstable : (prefixWord ++ tailWord_5975651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975651).length < 2 ^ (prefixWord ++ tailWord_5975651).sum := by decide
  have hdescent : baseEnd_5975651 < baseStart_5975651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975701 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 1, 7]
def baseStart_5975701 : Nat := 118140960795 + 5975701 * 2 ^ 59
def prefixEnd_5975701 : Nat := 4983230072969 + 3 ^ 40 * 5975701 * 2
def baseEnd_5975701 : Nat := 1022802286851009925351919

theorem tailTrace_5975701 : CollatzResearch.WordTrace tailWord_5975701 prefixEnd_5975701 1022802286851009925351919 := by
  unfold tailWord_5975701
  simp only [CollatzResearch.WordTrace]
  refine ⟨217951720924063320324302957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145301147282708880216201971 217951720924063320324302957)
  ·
    refine ⟨81731895346523745121613609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217951720924063320324302957 81731895346523745121613609)
    ·
      refine ⟨61298921509892808841210207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81731895346523745121613609 61298921509892808841210207)
      ·
        refine ⟨91948382264839213261815311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61298921509892808841210207 91948382264839213261815311)
        ·
          refine ⟨137922573397258819892722967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91948382264839213261815311 137922573397258819892722967)
          ·
            refine ⟨206883860095888229839084451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137922573397258819892722967 206883860095888229839084451)
            ·
              refine ⟨310325790143832344758626677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206883860095888229839084451 310325790143832344758626677)
              ·
                refine ⟨29093042825984282321121251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 310325790143832344758626677 29093042825984282321121251)
                ·
                  refine ⟨43639564238976423481681877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29093042825984282321121251 43639564238976423481681877)
                  ·
                    refine ⟨1022802286851009925351919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43639564238976423481681877 1022802286851009925351919)
                    ·
                      rfl

theorem cell23_5975701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_5975701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975701 prefixEnd_5975701 := by exact prefixLift 5975701
  have htrace : WordTrace (prefixWord ++ tailWord_5975701) baseStart_5975701 baseEnd_5975701 := by
    simpa [prefixWord, tailWord_5975701, baseEnd_5975701] using wordTrace_append hprefix tailTrace_5975701
  have hstable : (prefixWord ++ tailWord_5975701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975701).length < 2 ^ (prefixWord ++ tailWord_5975701).sum := by decide
  have hdescent : baseEnd_5975701 < baseStart_5975701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975725 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_5975725 : Nat := 118140960795 + 5975725 * 2 ^ 59
def prefixEnd_5975725 : Nat := 4983230072969 + 3 ^ 40 * 5975725 * 2
def baseEnd_5975725 : Nat := 3068419184088737682155647

theorem tailTrace_5975725 : CollatzResearch.WordTrace tailWord_5975725 prefixEnd_5975725 3068419184088737682155647 := by
  unfold tailWord_5975725
  simp only [CollatzResearch.WordTrace]
  refine ⟨217952596275976372423176629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145301730850650914948784419 217952596275976372423176629)
  ·
    refine ⟨20433055900872784914672809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217952596275976372423176629 20433055900872784914672809)
    ·
      refine ⟨15324791925654588686004607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20433055900872784914672809 15324791925654588686004607)
      ·
        refine ⟨22987187888481883029006911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15324791925654588686004607 22987187888481883029006911)
        ·
          refine ⟨34480781832722824543510367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22987187888481883029006911 34480781832722824543510367)
          ·
            refine ⟨51721172749084236815265551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34480781832722824543510367 51721172749084236815265551)
            ·
              refine ⟨77581759123626355222898327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51721172749084236815265551 77581759123626355222898327)
              ·
                refine ⟨116372638685439532834347491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77581759123626355222898327 116372638685439532834347491)
                ·
                  refine ⟨174558958028159299251521237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116372638685439532834347491 174558958028159299251521237)
                  ·
                    refine ⟨4091225578784983576207529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 174558958028159299251521237 4091225578784983576207529)
                    ·
                      refine ⟨3068419184088737682155647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4091225578784983576207529 3068419184088737682155647)
                      ·
                        rfl

theorem cell23_5975725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_5975725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975725 prefixEnd_5975725 := by exact prefixLift 5975725
  have htrace : WordTrace (prefixWord ++ tailWord_5975725) baseStart_5975725 baseEnd_5975725 := by
    simpa [prefixWord, tailWord_5975725, baseEnd_5975725] using wordTrace_append hprefix tailTrace_5975725
  have hstable : (prefixWord ++ tailWord_5975725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975725).length < 2 ^ (prefixWord ++ tailWord_5975725).sum := by decide
  have hdescent : baseEnd_5975725 < baseStart_5975725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975805 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 5, 1, 3]
def baseStart_5975805 : Nat := 118140960795 + 5975805 * 2 ^ 59
def prefixEnd_5975805 : Nat := 4983230072969 + 3 ^ 40 * 5975805 * 2
def baseEnd_5975805 : Nat := 3068460262541097369155279

theorem tailTrace_5975805 : CollatzResearch.WordTrace tailWord_5975805 prefixEnd_5975805 3068460262541097369155279 := by
  unfold tailWord_5975805
  simp only [CollatzResearch.WordTrace]
  refine ⟨217955514115686546086088869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145303676077124364057392579 217955514115686546086088869)
  ·
    refine ⟨40866658896691227391141663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217955514115686546086088869 40866658896691227391141663)
    ·
      refine ⟨61299988345036841086712495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40866658896691227391141663 61299988345036841086712495)
      ·
        refine ⟨91949982517555261630068743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61299988345036841086712495 91949982517555261630068743)
        ·
          refine ⟨137924973776332892445103115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91949982517555261630068743 137924973776332892445103115)
          ·
            refine ⟨206887460664499338667654673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137924973776332892445103115 206887460664499338667654673)
            ·
              refine ⟨155165595498374504000741005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206887460664499338667654673 155165595498374504000741005)
              ·
                refine ⟨58187098311890439000277877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155165595498374504000741005 58187098311890439000277877)
                ·
                  refine ⟨5455040466739728656276051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58187098311890439000277877 5455040466739728656276051)
                  ·
                    refine ⟨8182560700109592984414077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5455040466739728656276051 8182560700109592984414077)
                    ·
                      refine ⟨3068460262541097369155279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8182560700109592984414077 3068460262541097369155279)
                      ·
                        rfl

theorem cell23_5975805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_5975805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975805 prefixEnd_5975805 := by exact prefixLift 5975805
  have htrace : WordTrace (prefixWord ++ tailWord_5975805) baseStart_5975805 baseEnd_5975805 := by
    simpa [prefixWord, tailWord_5975805, baseEnd_5975805] using wordTrace_append hprefix tailTrace_5975805
  have hstable : (prefixWord ++ tailWord_5975805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975805).length < 2 ^ (prefixWord ++ tailWord_5975805).sum := by decide
  have hdescent : baseEnd_5975805 < baseStart_5975805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975855 : List Nat := [1, 1, 2, 1, 2, 1, 2, 7, 2, 4]
def baseStart_5975855 : Nat := 118140960795 + 5975855 * 2 ^ 59
def prefixEnd_5975855 : Nat := 4983230072969 + 3 ^ 40 * 5975855 * 2
def baseEnd_5975855 : Nat := 1022828645524607391176683

theorem tailTrace_5975855 : CollatzResearch.WordTrace tailWord_5975855 prefixEnd_5975855 1022828645524607391176683 := by
  unfold tailWord_5975855
  simp only [CollatzResearch.WordTrace]
  refine ⟨217957337765505404625409019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145304891843670269750272679 217957337765505404625409019)
  ·
    refine ⟨326936006648258106938113529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217957337765505404625409019 326936006648258106938113529)
    ·
      refine ⟨245202004986193580203585147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326936006648258106938113529 245202004986193580203585147)
      ·
        refine ⟨367803007479290370305377721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245202004986193580203585147 367803007479290370305377721)
        ·
          refine ⟨275852255609467777729033291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367803007479290370305377721 275852255609467777729033291)
          ·
            refine ⟨413778383414201666593549937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275852255609467777729033291 413778383414201666593549937)
            ·
              refine ⟨310333787560651249945162453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413778383414201666593549937 310333787560651249945162453)
              ·
                refine ⟨7273448145952763670589745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 310333787560651249945162453 7273448145952763670589745)
                ·
                  refine ⟨5455086109464572752942309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7273448145952763670589745 5455086109464572752942309)
                  ·
                    refine ⟨1022828645524607391176683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5455086109464572752942309 1022828645524607391176683)
                    ·
                      rfl

theorem cell23_5975855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 4].length) (baseStart_5975855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975855 prefixEnd_5975855 := by exact prefixLift 5975855
  have htrace : WordTrace (prefixWord ++ tailWord_5975855) baseStart_5975855 baseEnd_5975855 := by
    simpa [prefixWord, tailWord_5975855, baseEnd_5975855] using wordTrace_append hprefix tailTrace_5975855
  have hstable : (prefixWord ++ tailWord_5975855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975855).length < 2 ^ (prefixWord ++ tailWord_5975855).sum := by decide
  have hdescent : baseEnd_5975855 < baseStart_5975855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975859 : List Nat := [1, 1, 1, 2, 8, 1, 1, 2, 1, 5]
def baseStart_5975859 : Nat := 118140960795 + 5975859 * 2 ^ 59
def prefixEnd_5975859 : Nat := 4983230072969 + 3 ^ 40 * 5975859 * 2
def baseEnd_5975859 : Nat := 1022829330165480052626677

theorem tailTrace_5975859 : CollatzResearch.WordTrace tailWord_5975859 prefixEnd_5975859 1022829330165480052626677 := by
  unfold tailWord_5975859
  simp only [CollatzResearch.WordTrace]
  refine ⟨217957483657490913308554631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145304989104993942205703087 217957483657490913308554631)
  ·
    refine ⟨326936225486236369962831947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217957483657490913308554631 326936225486236369962831947)
    ·
      refine ⟨490404338229354554944247921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326936225486236369962831947 490404338229354554944247921)
      ·
        refine ⟨367803253672015916208185941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490404338229354554944247921 367803253672015916208185941)
        ·
          refine ⟨4310194378968936518064679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 367803253672015916208185941 4310194378968936518064679)
          ·
            refine ⟨6465291568453404777097019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4310194378968936518064679 6465291568453404777097019)
            ·
              refine ⟨9697937352680107165645529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6465291568453404777097019 9697937352680107165645529)
              ·
                refine ⟨7273453014510080374234147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9697937352680107165645529 7273453014510080374234147)
                ·
                  refine ⟨10910179521765120561351221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7273453014510080374234147 10910179521765120561351221)
                  ·
                    refine ⟨1022829330165480052626677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10910179521765120561351221 1022829330165480052626677)
                    ·
                      rfl

theorem cell23_5975859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 1, 5].length) (baseStart_5975859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975859 prefixEnd_5975859 := by exact prefixLift 5975859
  have htrace : WordTrace (prefixWord ++ tailWord_5975859) baseStart_5975859 baseEnd_5975859 := by
    simpa [prefixWord, tailWord_5975859, baseEnd_5975859] using wordTrace_append hprefix tailTrace_5975859
  have hstable : (prefixWord ++ tailWord_5975859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975859).length < 2 ^ (prefixWord ++ tailWord_5975859).sum := by decide
  have hdescent : baseEnd_5975859 < baseStart_5975859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975868 : List Nat := [2, 2, 2, 2, 1, 1, 4, 9]
def baseStart_5975868 : Nat := 118140960795 + 5975868 * 2 ^ 59
def prefixEnd_5975868 : Nat := 4983230072969 + 3 ^ 40 * 5975868 * 2
def baseEnd_5975868 : Nat := 113647874511938171209907

theorem tailTrace_5975868 : CollatzResearch.WordTrace tailWord_5975868 prefixEnd_5975868 113647874511938171209907 := by
  unfold tailWord_5975868
  simp only [CollatzResearch.WordTrace]
  refine ⟨108978905957229153922816129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145305207942972205230421505 108978905957229153922816129)
  ·
    refine ⟨81734179467921865442112097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108978905957229153922816129 81734179467921865442112097)
    ·
      refine ⟨61300634600941399081584073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81734179467921865442112097 61300634600941399081584073)
      ·
        refine ⟨45975475950706049311188055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61300634600941399081584073 45975475950706049311188055)
        ·
          refine ⟨68963213926059073966782083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45975475950706049311188055 68963213926059073966782083)
          ·
            refine ⟨103444820889088610950173125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68963213926059073966782083 103444820889088610950173125)
            ·
              refine ⟨19395903916704114553157461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103444820889088610950173125 19395903916704114553157461)
              ·
                refine ⟨113647874511938171209907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19395903916704114553157461 113647874511938171209907)
                ·
                  rfl

theorem cell23_5975868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 9].length) (baseStart_5975868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975868 prefixEnd_5975868 := by exact prefixLift 5975868
  have htrace : WordTrace (prefixWord ++ tailWord_5975868) baseStart_5975868 baseEnd_5975868 := by
    simpa [prefixWord, tailWord_5975868, baseEnd_5975868] using wordTrace_append hprefix tailTrace_5975868
  have hstable : (prefixWord ++ tailWord_5975868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975868).length < 2 ^ (prefixWord ++ tailWord_5975868).sum := by decide
  have hdescent : baseEnd_5975868 < baseStart_5975868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975875 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 4]
def baseStart_5975875 : Nat := 118140960795 + 5975875 * 2 ^ 59
def prefixEnd_5975875 : Nat := 4983230072969 + 3 ^ 40 * 5975875 * 2
def baseEnd_5975875 : Nat := 3068496206186912095279957

theorem tailTrace_5975875 : CollatzResearch.WordTrace tailWord_5975875 prefixEnd_5975875 3068496206186912095279957 := by
  unfold tailWord_5975875
  simp only [CollatzResearch.WordTrace]
  refine ⟨217958067225432948041137079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145305378150288632027424719 217958067225432948041137079)
  ·
    refine ⟨326937100838149422061705619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217958067225432948041137079 326937100838149422061705619)
    ·
      refine ⟨490405651257224133092558429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326937100838149422061705619 490405651257224133092558429)
      ·
        refine ⟨183902119221459049909709411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 490405651257224133092558429 183902119221459049909709411)
        ·
          refine ⟨275853178832188574864564117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183902119221459049909709411 275853178832188574864564117)
          ·
            refine ⟨12930617757758839446776443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 275853178832188574864564117 12930617757758839446776443)
            ·
              refine ⟨19395926636638259170164665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12930617757758839446776443 19395926636638259170164665)
              ·
                refine ⟨14546944977478694377623499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19395926636638259170164665 14546944977478694377623499)
                ·
                  refine ⟨21820417466218041566435249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14546944977478694377623499 21820417466218041566435249)
                  ·
                    refine ⟨16365313099663531174826437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21820417466218041566435249 16365313099663531174826437)
                    ·
                      refine ⟨3068496206186912095279957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16365313099663531174826437 3068496206186912095279957)
                      ·
                        rfl

theorem cell23_5975875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_5975875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975875 prefixEnd_5975875 := by exact prefixLift 5975875
  have htrace : WordTrace (prefixWord ++ tailWord_5975875) baseStart_5975875 baseEnd_5975875 := by
    simpa [prefixWord, tailWord_5975875, baseEnd_5975875] using wordTrace_append hprefix tailTrace_5975875
  have hstable : (prefixWord ++ tailWord_5975875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975875).length < 2 ^ (prefixWord ++ tailWord_5975875).sum := by decide
  have hdescent : baseEnd_5975875 < baseStart_5975875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975885 : List Nat := [1, 6, 1, 2, 1, 12]
def baseStart_5975885 : Nat := 118140960795 + 5975885 * 2 ^ 59
def prefixEnd_5975885 : Nat := 4983230072969 + 3 ^ 40 * 5975885 * 2
def baseEnd_5975885 : Nat := 12627577534952498173477

theorem tailTrace_5975885 : CollatzResearch.WordTrace tailWord_5975885 prefixEnd_5975885 12627577534952498173477 := by
  unfold tailWord_5975885
  simp only [CollatzResearch.WordTrace]
  refine ⟨217958431955396719749001109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145305621303597813166000739 217958431955396719749001109)
  ·
    refine ⟨10216801497909221238234427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 217958431955396719749001109 10216801497909221238234427)
    ·
      refine ⟨15325202246863831857351641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10216801497909221238234427 15325202246863831857351641)
      ·
        refine ⟨11493901685147873893013731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15325202246863831857351641 11493901685147873893013731)
        ·
          refine ⟨17240852527721810839520597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11493901685147873893013731 17240852527721810839520597)
          ·
            refine ⟨12627577534952498173477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 17240852527721810839520597 12627577534952498173477)
            ·
              rfl

theorem cell23_5975885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 12].length) (baseStart_5975885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975885 prefixEnd_5975885 := by exact prefixLift 5975885
  have htrace : WordTrace (prefixWord ++ tailWord_5975885) baseStart_5975885 baseEnd_5975885 := by
    simpa [prefixWord, tailWord_5975885, baseEnd_5975885] using wordTrace_append hprefix tailTrace_5975885
  have hstable : (prefixWord ++ tailWord_5975885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975885).length < 2 ^ (prefixWord ++ tailWord_5975885).sum := by decide
  have hdescent : baseEnd_5975885 < baseStart_5975885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975898 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 1, 9]
def baseStart_5975898 : Nat := 118140960795 + 5975898 * 2 ^ 59
def prefixEnd_5975898 : Nat := 4983230072969 + 3 ^ 40 * 5975898 * 2
def baseEnd_5975898 : Nat := 1022836005413988501764117

theorem tailTrace_5975898 : CollatzResearch.WordTrace tailWord_5975898 prefixEnd_5975898 1022836005413988501764117 := by
  unfold tailWord_5975898
  simp only [CollatzResearch.WordTrace]
  refine ⟨54489726526087405742306087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145305937402899748646149565 54489726526087405742306087)
  ·
    refine ⟨81734589789131108613459131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54489726526087405742306087 81734589789131108613459131)
    ·
      refine ⟨122601884683696662920188697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81734589789131108613459131 122601884683696662920188697)
      ·
        refine ⟨91951413512772497190141523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122601884683696662920188697 91951413512772497190141523)
        ·
          refine ⟨137927120269158745785212285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91951413512772497190141523 137927120269158745785212285)
          ·
            refine ⟨51722670100934529669454607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137927120269158745785212285 51722670100934529669454607)
            ·
              refine ⟨77584005151401794504181911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51722670100934529669454607 77584005151401794504181911)
              ·
                refine ⟨116376007727102691756272867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77584005151401794504181911 116376007727102691756272867)
                ·
                  refine ⟨174564011590654037634409301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116376007727102691756272867 174564011590654037634409301)
                  ·
                    refine ⟨1022836005413988501764117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 174564011590654037634409301 1022836005413988501764117)
                    ·
                      rfl

theorem cell23_5975898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_5975898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975898 prefixEnd_5975898 := by exact prefixLift 5975898
  have htrace : WordTrace (prefixWord ++ tailWord_5975898) baseStart_5975898 baseEnd_5975898 := by
    simpa [prefixWord, tailWord_5975898, baseEnd_5975898] using wordTrace_append hprefix tailTrace_5975898
  have hstable : (prefixWord ++ tailWord_5975898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975898).length < 2 ^ (prefixWord ++ tailWord_5975898).sum := by decide
  have hdescent : baseEnd_5975898 < baseStart_5975898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975912 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_5975912 : Nat := 118140960795 + 5975912 * 2 ^ 59
def prefixEnd_5975912 : Nat := 4983230072969 + 3 ^ 40 * 5975912 * 2
def baseEnd_5975912 : Nat := 3068515204971128450517287

theorem tailTrace_5975912 : CollatzResearch.WordTrace tailWord_5975912 prefixEnd_5975912 3068515204971128450517287 := by
  unfold tailWord_5975912
  simp only [CollatzResearch.WordTrace]
  refine ⟨108979708363149451680116995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145306277817532602240155993 108979708363149451680116995)
  ·
    refine ⟨163469562544724177520175493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108979708363149451680116995 163469562544724177520175493)
    ·
      refine ⟨30650542977135783285032905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163469562544724177520175493 30650542977135783285032905)
      ·
        refine ⟨22987907232851837463774679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30650542977135783285032905 22987907232851837463774679)
        ·
          refine ⟨34481860849277756195662019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22987907232851837463774679 34481860849277756195662019)
          ·
            refine ⟨51722791273916634293493029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34481860849277756195662019 51722791273916634293493029)
            ·
              refine ⟨9698023363859368930029943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51722791273916634293493029 9698023363859368930029943)
              ·
                refine ⟨14547035045789053395044915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9698023363859368930029943 14547035045789053395044915)
                ·
                  refine ⟨21820552568683580092567373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14547035045789053395044915 21820552568683580092567373)
                  ·
                    refine ⟨8182707213256342534712765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21820552568683580092567373 8182707213256342534712765)
                    ·
                      refine ⟨3068515204971128450517287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8182707213256342534712765 3068515204971128450517287)
                      ·
                        rfl

theorem cell23_5975912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_5975912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975912 prefixEnd_5975912 := by exact prefixLift 5975912
  have htrace : WordTrace (prefixWord ++ tailWord_5975912) baseStart_5975912 baseEnd_5975912 := by
    simpa [prefixWord, tailWord_5975912, baseEnd_5975912] using wordTrace_append hprefix tailTrace_5975912
  have hstable : (prefixWord ++ tailWord_5975912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975912).length < 2 ^ (prefixWord ++ tailWord_5975912).sum := by decide
  have hdescent : baseEnd_5975912 < baseStart_5975912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975925 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_5975925 : Nat := 118140960795 + 5975925 * 2 ^ 59
def prefixEnd_5975925 : Nat := 4983230072969 + 3 ^ 40 * 5975925 * 2
def baseEnd_5975925 : Nat := 3068521880219636899654727

theorem tailTrace_5975925 : CollatzResearch.WordTrace tailWord_5975925 prefixEnd_5975925 3068521880219636899654727 := by
  unfold tailWord_5975925
  simp only [CollatzResearch.WordTrace]
  refine ⟨217959890875251806580457229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145306593916834537720304819 217959890875251806580457229)
  ·
    refine ⟨81734959078219427467671461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217959890875251806580457229 81734959078219427467671461)
    ·
      refine ⟨15325304827166142650188399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81734959078219427467671461 15325304827166142650188399)
      ·
        refine ⟨22987957240749213975282599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15325304827166142650188399 22987957240749213975282599)
        ·
          refine ⟨34481935861123820962923899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22987957240749213975282599 34481935861123820962923899)
          ·
            refine ⟨51722903791685731444385849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34481935861123820962923899 51722903791685731444385849)
            ·
              refine ⟨38792177843764298583289387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51722903791685731444385849 38792177843764298583289387)
              ·
                refine ⟨58188266765646447874934081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38792177843764298583289387 58188266765646447874934081)
                ·
                  refine ⟨43641200074234835906200561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58188266765646447874934081 43641200074234835906200561)
                  ·
                    refine ⟨32730900055676126929650421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43641200074234835906200561 32730900055676126929650421)
                    ·
                      refine ⟨3068521880219636899654727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32730900055676126929650421 3068521880219636899654727)
                      ·
                        rfl

theorem cell23_5975925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_5975925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975925 prefixEnd_5975925 := by exact prefixLift 5975925
  have htrace : WordTrace (prefixWord ++ tailWord_5975925) baseStart_5975925 baseEnd_5975925 := by
    simpa [prefixWord, tailWord_5975925, baseEnd_5975925] using wordTrace_append hprefix tailTrace_5975925
  have hstable : (prefixWord ++ tailWord_5975925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975925).length < 2 ^ (prefixWord ++ tailWord_5975925).sum := by decide
  have hdescent : baseEnd_5975925 < baseStart_5975925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5975939 : List Nat := [1, 1, 1, 3, 4, 3, 1, 3, 1, 3, 2]
def baseStart_5975939 : Nat := 118140960795 + 5975939 * 2 ^ 59
def prefixEnd_5975939 : Nat := 4983230072969 + 3 ^ 40 * 5975939 * 2
def baseEnd_5975939 : Nat := 3068529068948799844879663

theorem tailTrace_5975939 : CollatzResearch.WordTrace tailWord_5975939 prefixEnd_5975939 3068529068948799844879663 := by
  unfold tailWord_5975939
  simp only [CollatzResearch.WordTrace]
  refine ⟨217960401497201086971466871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145306934331467391314311247 217960401497201086971466871)
  ·
    refine ⟨326940602245801630457200307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217960401497201086971466871 326940602245801630457200307)
    ·
      refine ⟨490410903368702445685800461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326940602245801630457200307 490410903368702445685800461)
      ·
        refine ⟨183904088763263417132175173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 490410903368702445685800461 183904088763263417132175173)
        ·
          refine ⟨34482016643111890712282845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183904088763263417132175173 34482016643111890712282845)
          ·
            refine ⟨12930756241166959017106067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34482016643111890712282845 12930756241166959017106067)
            ·
              refine ⟨19396134361750438525659101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12930756241166959017106067 19396134361750438525659101)
              ·
                refine ⟨7273550385656414447122163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19396134361750438525659101 7273550385656414447122163)
                ·
                  refine ⟨10910325578484621670683245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7273550385656414447122163 10910325578484621670683245)
                  ·
                    refine ⟨4091372091931733126506217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10910325578484621670683245 4091372091931733126506217)
                    ·
                      refine ⟨3068529068948799844879663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4091372091931733126506217 3068529068948799844879663)
                      ·
                        rfl

theorem cell23_5975939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 3, 2].length) (baseStart_5975939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5975939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5975939 prefixEnd_5975939 := by exact prefixLift 5975939
  have htrace : WordTrace (prefixWord ++ tailWord_5975939) baseStart_5975939 baseEnd_5975939 := by
    simpa [prefixWord, tailWord_5975939, baseEnd_5975939] using wordTrace_append hprefix tailTrace_5975939
  have hstable : (prefixWord ++ tailWord_5975939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5975939).length < 2 ^ (prefixWord ++ tailWord_5975939).sum := by decide
  have hdescent : baseEnd_5975939 < baseStart_5975939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5975939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976015 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 5]
def baseStart_5976015 : Nat := 118140960795 + 5976015 * 2 ^ 59
def prefixEnd_5976015 : Nat := 4983230072969 + 3 ^ 40 * 5976015 * 2
def baseEnd_5976015 : Nat := 3068568093478541547529313

theorem tailTrace_5976015 : CollatzResearch.WordTrace tailWord_5976015 prefixEnd_5976015 3068568093478541547529313 := by
  unfold tailWord_5976015
  simp only [CollatzResearch.WordTrace]
  refine ⟨217963173444925751951233499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145308782296617167967488999 217963173444925751951233499)
  ·
    refine ⟨326944760167388627926850249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217963173444925751951233499 326944760167388627926850249)
    ·
      refine ⟨245208570125541470945137687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326944760167388627926850249 245208570125541470945137687)
      ·
        refine ⟨367812855188312206417706531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245208570125541470945137687 367812855188312206417706531)
        ·
          refine ⟨551719282782468309626559797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367812855188312206417706531 551719282782468309626559797)
          ·
            refine ⟨51723682760856404027489981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 551719282782468309626559797 51723682760856404027489981)
            ·
              refine ⟨19396381035321151510308743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51723682760856404027489981 19396381035321151510308743)
              ·
                refine ⟨29094571552981727265463115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19396381035321151510308743 29094571552981727265463115)
                ·
                  refine ⟨43641857329472590898194673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29094571552981727265463115 43641857329472590898194673)
                  ·
                    refine ⟨32731392997104443173646005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43641857329472590898194673 32731392997104443173646005)
                    ·
                      refine ⟨3068568093478541547529313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32731392997104443173646005 3068568093478541547529313)
                      ·
                        rfl

theorem cell23_5976015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_5976015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976015 prefixEnd_5976015 := by exact prefixLift 5976015
  have htrace : WordTrace (prefixWord ++ tailWord_5976015) baseStart_5976015 baseEnd_5976015 := by
    simpa [prefixWord, tailWord_5976015, baseEnd_5976015] using wordTrace_append hprefix tailTrace_5976015
  have hstable : (prefixWord ++ tailWord_5976015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976015).length < 2 ^ (prefixWord ++ tailWord_5976015).sum := by decide
  have hdescent : baseEnd_5976015 < baseStart_5976015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976039 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 2, 5]
def baseStart_5976039 : Nat := 118140960795 + 5976039 * 2 ^ 59
def prefixEnd_5976039 : Nat := 4983230072969 + 3 ^ 40 * 5976039 * 2
def baseEnd_5976039 : Nat := 1022860139004749817876401

theorem tailTrace_5976039 : CollatzResearch.WordTrace tailWord_5976039 prefixEnd_5976039 1022860139004749817876401 := by
  unfold tailWord_5976039
  simp only [CollatzResearch.WordTrace]
  refine ⟨217964048796838804050107171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145309365864559202700071447 217964048796838804050107171)
  ·
    refine ⟨326946073195258206075160757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217964048796838804050107171 326946073195258206075160757)
    ·
      refine ⟨30651194362055456819546321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 326946073195258206075160757 30651194362055456819546321)
      ·
        refine ⟨22988395771541592614659741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30651194362055456819546321 22988395771541592614659741)
        ·
          refine ⟨8620648414328097230497403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22988395771541592614659741 8620648414328097230497403)
          ·
            refine ⟨12930972621492145845746105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8620648414328097230497403 12930972621492145845746105)
            ·
              refine ⟨9698229466119109384309579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12930972621492145845746105 9698229466119109384309579)
              ·
                refine ⟨14547344199178664076464369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9698229466119109384309579 14547344199178664076464369)
                ·
                  refine ⟨10910508149383998057348277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14547344199178664076464369 10910508149383998057348277)
                  ·
                    refine ⟨1022860139004749817876401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10910508149383998057348277 1022860139004749817876401)
                    ·
                      rfl

theorem cell23_5976039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_5976039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976039 prefixEnd_5976039 := by exact prefixLift 5976039
  have htrace : WordTrace (prefixWord ++ tailWord_5976039) baseStart_5976039 baseEnd_5976039 := by
    simpa [prefixWord, tailWord_5976039, baseEnd_5976039] using wordTrace_append hprefix tailTrace_5976039
  have hstable : (prefixWord ++ tailWord_5976039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976039).length < 2 ^ (prefixWord ++ tailWord_5976039).sum := by decide
  have hdescent : baseEnd_5976039 < baseStart_5976039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976070 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_5976070 : Nat := 118140960795 + 5976070 * 2 ^ 59
def prefixEnd_5976070 : Nat := 4983230072969 + 3 ^ 40 * 5976070 * 2
def baseEnd_5976070 : Nat := 3068596334914538832341561

theorem tailTrace_5976070 : CollatzResearch.WordTrace tailWord_5976070 prefixEnd_5976070 3068596334914538832341561 := by
  unfold tailWord_5976070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6811411858116453010765177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145310119639817664229657109 6811411858116453010765177)
  ·
    refine ⟨5108558893587339758073883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6811411858116453010765177 5108558893587339758073883)
    ·
      refine ⟨7662838340381009637110825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5108558893587339758073883 7662838340381009637110825)
      ·
        refine ⟨5747128755285757227833119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7662838340381009637110825 5747128755285757227833119)
        ·
          refine ⟨8620693132928635841749679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5747128755285757227833119 8620693132928635841749679)
          ·
            refine ⟨12931039699392953762624519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8620693132928635841749679 12931039699392953762624519)
            ·
              refine ⟨19396559549089430643936779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12931039699392953762624519 19396559549089430643936779)
              ·
                refine ⟨29094839323634145965905169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19396559549089430643936779 29094839323634145965905169)
                ·
                  refine ⟨21821129492725609474428877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29094839323634145965905169 21821129492725609474428877)
                  ·
                    refine ⟨8182923559772103552910829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21821129492725609474428877 8182923559772103552910829)
                    ·
                      refine ⟨3068596334914538832341561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8182923559772103552910829 3068596334914538832341561)
                      ·
                        rfl

theorem cell23_5976070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_5976070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976070 prefixEnd_5976070 := by exact prefixLift 5976070
  have htrace : WordTrace (prefixWord ++ tailWord_5976070) baseStart_5976070 baseEnd_5976070 := by
    simpa [prefixWord, tailWord_5976070, baseEnd_5976070] using wordTrace_append hprefix tailTrace_5976070
  have hstable : (prefixWord ++ tailWord_5976070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976070).length < 2 ^ (prefixWord ++ tailWord_5976070).sum := by decide
  have hdescent : baseEnd_5976070 < baseStart_5976070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976119 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 2, 3, 2]
def baseStart_5976119 : Nat := 118140960795 + 5976119 * 2 ^ 59
def prefixEnd_5976119 : Nat := 4983230072969 + 3 ^ 40 * 5976119 * 2
def baseEnd_5976119 : Nat := 3068621495466609140628835

theorem tailTrace_5976119 : CollatzResearch.WordTrace tailWord_5976119 prefixEnd_5976119 3068621495466609140628835 := by
  unfold tailWord_5976119
  simp only [CollatzResearch.WordTrace]
  refine ⟨217966966636548977713019411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145311311091032651808679607 217966966636548977713019411)
  ·
    refine ⟨326950449954823466569529117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217966966636548977713019411 326950449954823466569529117)
    ·
      refine ⟨122606418733058799963573419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326950449954823466569529117 122606418733058799963573419)
      ·
        refine ⟨183909628099588199945360129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122606418733058799963573419 183909628099588199945360129)
        ·
          refine ⟨137932221074691149959020097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183909628099588199945360129 137932221074691149959020097)
          ·
            refine ⟨103449165806018362469265073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137932221074691149959020097 103449165806018362469265073)
            ·
              refine ⟨77586874354513771851948805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103449165806018362469265073 77586874354513771851948805)
              ·
                refine ⟨14547538941471332222240401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77586874354513771851948805 14547538941471332222240401)
                ·
                  refine ⟨10910654206103499166680301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14547538941471332222240401 10910654206103499166680301)
                  ·
                    refine ⟨4091495327288812187505113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10910654206103499166680301 4091495327288812187505113)
                    ·
                      refine ⟨3068621495466609140628835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4091495327288812187505113 3068621495466609140628835)
                      ·
                        rfl

theorem cell23_5976119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 3, 2].length) (baseStart_5976119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976119 prefixEnd_5976119 := by exact prefixLift 5976119
  have htrace : WordTrace (prefixWord ++ tailWord_5976119) baseStart_5976119 baseEnd_5976119 := by
    simpa [prefixWord, tailWord_5976119, baseEnd_5976119] using wordTrace_append hprefix tailTrace_5976119
  have hstable : (prefixWord ++ tailWord_5976119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976119).length < 2 ^ (prefixWord ++ tailWord_5976119).sum := by decide
  have hdescent : baseEnd_5976119 < baseStart_5976119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976146 : List Nat := [3, 2, 2, 1, 4, 1, 2, 2, 1, 5]
def baseStart_5976146 : Nat := 118140960795 + 5976146 * 2 ^ 59
def prefixEnd_5976146 : Nat := 4983230072969 + 3 ^ 40 * 5976146 * 2
def baseEnd_5976146 : Nat := 1022878453148093511663737

theorem tailTrace_5976146 : CollatzResearch.WordTrace tailWord_5976146 prefixEnd_5976146 1022878453148093511663737 := by
  unfold tailWord_5976146
  simp only [CollatzResearch.WordTrace]
  refine ⟨54491987851862790331063073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145311967604967440882834861 54491987851862790331063073)
  ·
    refine ⟨40868990888897092748297305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54491987851862790331063073 40868990888897092748297305)
    ·
      refine ⟨30651743166672819561222979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40868990888897092748297305 30651743166672819561222979)
      ·
        refine ⟨45977614750009229341834469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30651743166672819561222979 45977614750009229341834469)
        ·
          refine ⟨8620802765626730501593963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45977614750009229341834469 8620802765626730501593963)
          ·
            refine ⟨12931204148440095752390945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8620802765626730501593963 12931204148440095752390945)
            ·
              refine ⟨9698403111330071814293209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12931204148440095752390945 9698403111330071814293209)
              ·
                refine ⟨7273802333497553860719907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9698403111330071814293209 7273802333497553860719907)
                ·
                  refine ⟨10910703500246330791079861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7273802333497553860719907 10910703500246330791079861)
                  ·
                    refine ⟨1022878453148093511663737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10910703500246330791079861 1022878453148093511663737)
                    ·
                      rfl

theorem cell23_5976146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_5976146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976146 prefixEnd_5976146 := by exact prefixLift 5976146
  have htrace : WordTrace (prefixWord ++ tailWord_5976146) baseStart_5976146 baseEnd_5976146 := by
    simpa [prefixWord, tailWord_5976146, baseEnd_5976146] using wordTrace_append hprefix tailTrace_5976146
  have hstable : (prefixWord ++ tailWord_5976146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976146).length < 2 ^ (prefixWord ++ tailWord_5976146).sum := by decide
  have hdescent : baseEnd_5976146 < baseStart_5976146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976149 : List Nat := [1, 3, 2, 2, 1, 3, 1, 4, 1, 1, 4]
def baseStart_5976149 : Nat := 118140960795 + 5976149 * 2 ^ 59
def prefixEnd_5976149 : Nat := 4983230072969 + 3 ^ 40 * 5976149 * 2
def baseEnd_5976149 : Nat := 3068636899886244023253697

theorem tailTrace_5976149 : CollatzResearch.WordTrace tailWord_5976149 prefixEnd_5976149 3068636899886244023253697 := by
  unfold tailWord_5976149
  simp only [CollatzResearch.WordTrace]
  refine ⟨217968060826440292836611501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145312040550960195224407667 217968060826440292836611501)
  ·
    refine ⟨81738022809915109813729313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217968060826440292836611501 81738022809915109813729313)
    ·
      refine ⟨61303517107436332360296985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81738022809915109813729313 61303517107436332360296985)
      ·
        refine ⟨45977637830577249270222739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61303517107436332360296985 45977637830577249270222739)
        ·
          refine ⟨68966456745865873905334109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45977637830577249270222739 68966456745865873905334109)
          ·
            refine ⟨25862421279699702714500291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68966456745865873905334109 25862421279699702714500291)
            ·
              refine ⟨38793631919549554071750437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25862421279699702714500291 38793631919549554071750437)
              ·
                refine ⟨7273805984915541388453207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38793631919549554071750437 7273805984915541388453207)
                ·
                  refine ⟨10910708977373312082679811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7273805984915541388453207 10910708977373312082679811)
                  ·
                    refine ⟨16366063466059968124019717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10910708977373312082679811 16366063466059968124019717)
                    ·
                      refine ⟨3068636899886244023253697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16366063466059968124019717 3068636899886244023253697)
                      ·
                        rfl

theorem cell23_5976149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_5976149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976149 prefixEnd_5976149 := by exact prefixLift 5976149
  have htrace : WordTrace (prefixWord ++ tailWord_5976149) baseStart_5976149 baseEnd_5976149 := by
    simpa [prefixWord, tailWord_5976149, baseEnd_5976149] using wordTrace_append hprefix tailTrace_5976149
  have hstable : (prefixWord ++ tailWord_5976149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976149).length < 2 ^ (prefixWord ++ tailWord_5976149).sum := by decide
  have hdescent : baseEnd_5976149 < baseStart_5976149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976169 : List Nat := [1, 2, 1, 1, 1, 5, 1, 5, 1, 2, 3]
def baseStart_5976169 : Nat := 118140960795 + 5976169 * 2 ^ 59
def prefixEnd_5976169 : Nat := 4983230072969 + 3 ^ 40 * 5976169 * 2
def baseEnd_5976169 : Nat := 3068647169499333945003605

theorem tailTrace_5976169 : CollatzResearch.WordTrace tailWord_5976169 prefixEnd_5976169 3068647169499333945003605 := by
  unfold tailWord_5976169
  simp only [CollatzResearch.WordTrace]
  refine ⟨217968790286367836252339561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145312526857578557501559707 217968790286367836252339561)
  ·
    refine ⟨163476592714775877189254671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217968790286367836252339561 163476592714775877189254671)
    ·
      refine ⟨245214889072163815783882007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163476592714775877189254671 245214889072163815783882007)
      ·
        refine ⟨367822333608245723675823011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245214889072163815783882007 367822333608245723675823011)
        ·
          refine ⟨551733500412368585513734517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367822333608245723675823011 551733500412368585513734517)
          ·
            refine ⟨51725015663659554891912611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 551733500412368585513734517 51725015663659554891912611)
            ·
              refine ⟨77587523495489332337868917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51725015663659554891912611 77587523495489332337868917)
              ·
                refine ⟨7273830327702124906675211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77587523495489332337868917 7273830327702124906675211)
                ·
                  refine ⟨10910745491553187360012817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7273830327702124906675211 10910745491553187360012817)
                  ·
                    refine ⟨8183059118664890520009613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10910745491553187360012817 8183059118664890520009613)
                    ·
                      refine ⟨3068647169499333945003605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8183059118664890520009613 3068647169499333945003605)
                      ·
                        rfl

theorem cell23_5976169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 2, 3].length) (baseStart_5976169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976169 prefixEnd_5976169 := by exact prefixLift 5976169
  have htrace : WordTrace (prefixWord ++ tailWord_5976169) baseStart_5976169 baseEnd_5976169 := by
    simpa [prefixWord, tailWord_5976169, baseEnd_5976169] using wordTrace_append hprefix tailTrace_5976169
  have hstable : (prefixWord ++ tailWord_5976169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976169).length < 2 ^ (prefixWord ++ tailWord_5976169).sum := by decide
  have hdescent : baseEnd_5976169 < baseStart_5976169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976172 : List Nat := [2, 2, 1, 1, 3, 5, 9]
def baseStart_5976172 : Nat := 118140960795 + 5976172 * 2 ^ 59
def prefixEnd_5976172 : Nat := 4983230072969 + 3 ^ 40 * 5976172 * 2
def baseEnd_5976172 : Nat := 37884551974583918929211

theorem tailTrace_5976172 : CollatzResearch.WordTrace tailWord_5976172 prefixEnd_5976172 37884551974583918929211 := by
  unfold tailWord_5976172
  simp only [CollatzResearch.WordTrace]
  refine ⟨108984449852678483882349385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145312599803571311843132513 108984449852678483882349385)
  ·
    refine ⟨81738337389508862911762039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108984449852678483882349385 81738337389508862911762039)
    ·
      refine ⟨122607506084263294367643059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81738337389508862911762039 122607506084263294367643059)
      ·
        refine ⟨183911259126394941551464589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122607506084263294367643059 183911259126394941551464589)
        ·
          refine ⟨68966722172398103081799221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183911259126394941551464589 68966722172398103081799221)
          ·
            refine ⟨6465630203662322163918677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68966722172398103081799221 6465630203662322163918677)
            ·
              refine ⟨37884551974583918929211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6465630203662322163918677 37884551974583918929211)
              ·
                rfl

theorem cell23_5976172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 9].length) (baseStart_5976172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976172 prefixEnd_5976172 := by exact prefixLift 5976172
  have htrace : WordTrace (prefixWord ++ tailWord_5976172) baseStart_5976172 baseEnd_5976172 := by
    simpa [prefixWord, tailWord_5976172, baseEnd_5976172] using wordTrace_append hprefix tailTrace_5976172
  have hstable : (prefixWord ++ tailWord_5976172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976172).length < 2 ^ (prefixWord ++ tailWord_5976172).sum := by decide
  have hdescent : baseEnd_5976172 < baseStart_5976172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976183 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 3, 2, 2]
def baseStart_5976183 : Nat := 118140960795 + 5976183 * 2 ^ 59
def prefixEnd_5976183 : Nat := 4983230072969 + 3 ^ 40 * 5976183 * 2
def baseEnd_5976183 : Nat := 3068654358228496890228541

theorem tailTrace_5976183 : CollatzResearch.WordTrace tailWord_5976183 prefixEnd_5976183 3068654358228496890228541 := by
  unfold tailWord_5976183
  simp only [CollatzResearch.WordTrace]
  refine ⟨217969300908317116643349203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145312867272211411095566135 217969300908317116643349203)
  ·
    refine ⟨326953951362475674965023805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217969300908317116643349203 326953951362475674965023805)
    ·
      refine ⟨122607731760928378111883927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326953951362475674965023805 122607731760928378111883927)
      ·
        refine ⟨183911597641392567167825891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122607731760928378111883927 183911597641392567167825891)
        ·
          refine ⟨275867396462088850751738837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183911597641392567167825891 275867396462088850751738837)
          ·
            refine ⟨6465642104580207439493879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 275867396462088850751738837 6465642104580207439493879)
            ·
              refine ⟨9698463156870311159240819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6465642104580207439493879 9698463156870311159240819)
              ·
                refine ⟨14547694735305466738861229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9698463156870311159240819 14547694735305466738861229)
                ·
                  refine ⟨5455385525739550027072961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14547694735305466738861229 5455385525739550027072961)
                  ·
                    refine ⟨4091539144304662520304721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5455385525739550027072961 4091539144304662520304721)
                    ·
                      refine ⟨3068654358228496890228541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4091539144304662520304721 3068654358228496890228541)
                      ·
                        rfl

theorem cell23_5976183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 2, 2].length) (baseStart_5976183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976183 prefixEnd_5976183 := by exact prefixLift 5976183
  have htrace : WordTrace (prefixWord ++ tailWord_5976183) baseStart_5976183 baseEnd_5976183 := by
    simpa [prefixWord, tailWord_5976183, baseEnd_5976183] using wordTrace_append hprefix tailTrace_5976183
  have hstable : (prefixWord ++ tailWord_5976183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976183).length < 2 ^ (prefixWord ++ tailWord_5976183).sum := by decide
  have hdescent : baseEnd_5976183 < baseStart_5976183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976214 : List Nat := [5, 3, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_5976214 : Nat := 118140960795 + 5976214 * 2 ^ 59
def prefixEnd_5976214 : Nat := 4983230072969 + 3 ^ 40 * 5976214 * 2
def baseEnd_5976214 : Nat := 1022890092042928756313633

theorem tailTrace_5976214 : CollatzResearch.WordTrace tailWord_5976214 prefixEnd_5976214 1022890092042928756313633 := by
  unfold tailWord_5976214
  simp only [CollatzResearch.WordTrace]
  refine ⟨13623151973200300558607981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145313621047469872625151797 13623151973200300558607981)
  ·
    refine ⟨5108681989950112709477993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13623151973200300558607981 5108681989950112709477993)
    ·
      refine ⟨3831511492462584532108495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5108681989950112709477993 3831511492462584532108495)
      ·
        refine ⟨5747267238693876798162743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3831511492462584532108495 5747267238693876798162743)
        ·
          refine ⟨8620900858040815197244115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5747267238693876798162743 8620900858040815197244115)
          ·
            refine ⟨12931351287061222795866173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8620900858040815197244115 12931351287061222795866173)
            ·
              refine ⟨4849256732647958548449815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12931351287061222795866173 4849256732647958548449815)
              ·
                refine ⟨7273885098971937822674723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4849256732647958548449815 7273885098971937822674723)
                ·
                  refine ⟨10910827648457906734012085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7273885098971937822674723 10910827648457906734012085)
                  ·
                    refine ⟨1022890092042928756313633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10910827648457906734012085 1022890092042928756313633)
                    ·
                      rfl

theorem cell23_5976214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_5976214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976214 prefixEnd_5976214 := by exact prefixLift 5976214
  have htrace : WordTrace (prefixWord ++ tailWord_5976214) baseStart_5976214 baseEnd_5976214 := by
    simpa [prefixWord, tailWord_5976214, baseEnd_5976214] using wordTrace_append hprefix tailTrace_5976214
  have hstable : (prefixWord ++ tailWord_5976214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976214).length < 2 ^ (prefixWord ++ tailWord_5976214).sum := by decide
  have hdescent : baseEnd_5976214 < baseStart_5976214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976216 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 1, 3, 3]
def baseStart_5976216 : Nat := 118140960795 + 5976216 * 2 ^ 59
def prefixEnd_5976216 : Nat := 4983230072969 + 3 ^ 40 * 5976216 * 2
def baseEnd_5976216 : Nat := 3068671303090095261115889

theorem tailTrace_5976216 : CollatzResearch.WordTrace tailWord_5976216 prefixEnd_5976216 3068671303090095261115889 := by
  unfold tailWord_5976216
  simp only [CollatzResearch.WordTrace]
  refine ⟨108985252258598781639650251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145313669678131708852867001 108985252258598781639650251)
  ·
    refine ⟨163477878387898172459475377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108985252258598781639650251 163477878387898172459475377)
    ·
      refine ⟨122608408790923629344606533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163477878387898172459475377 122608408790923629344606533)
      ·
        refine ⟨22989076648298180502113725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122608408790923629344606533 22989076648298180502113725)
        ·
          refine ⟨8620903743111817688292647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22989076648298180502113725 8620903743111817688292647)
          ·
            refine ⟨12931355614667726532438971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8620903743111817688292647 12931355614667726532438971)
            ·
              refine ⟨19397033422001589798658457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12931355614667726532438971 19397033422001589798658457)
              ·
                refine ⟨14547775066501192348993843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19397033422001589798658457 14547775066501192348993843)
                ·
                  refine ⟨21821662599751788523490765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14547775066501192348993843 21821662599751788523490765)
                  ·
                    refine ⟨8183123474906920696309037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21821662599751788523490765 8183123474906920696309037)
                    ·
                      refine ⟨3068671303090095261115889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8183123474906920696309037 3068671303090095261115889)
                      ·
                        rfl

theorem cell23_5976216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_5976216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976216 prefixEnd_5976216 := by exact prefixLift 5976216
  have htrace : WordTrace (prefixWord ++ tailWord_5976216) baseStart_5976216 baseEnd_5976216 := by
    simpa [prefixWord, tailWord_5976216, baseEnd_5976216] using wordTrace_append hprefix tailTrace_5976216
  have hstable : (prefixWord ++ tailWord_5976216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976216).length < 2 ^ (prefixWord ++ tailWord_5976216).sum := by decide
  have hdescent : baseEnd_5976216 < baseStart_5976216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976239 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 5, 4, 2]
def baseStart_5976239 : Nat := 118140960795 + 5976239 * 2 ^ 59
def prefixEnd_5976239 : Nat := 4983230072969 + 3 ^ 40 * 5976239 * 2
def baseEnd_5976239 : Nat := 3068683113145148671128283

theorem tailTrace_5976239 : CollatzResearch.WordTrace tailWord_5976239 prefixEnd_5976239 3068683113145148671128283 := by
  unfold tailWord_5976239
  simp only [CollatzResearch.WordTrace]
  refine ⟨217971343396114238207387771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145314228930742825471591847 217971343396114238207387771)
  ·
    refine ⟨326957015094171357311081657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217971343396114238207387771 326957015094171357311081657)
    ·
      refine ⟨245217761320628517983311243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326957015094171357311081657 245217761320628517983311243)
      ·
        refine ⟨367826641980942776974966865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245217761320628517983311243 367826641980942776974966865)
        ·
          refine ⟨275869981485707082731225149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367826641980942776974966865 275869981485707082731225149)
          ·
            refine ⟨103451243057140156024209431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275869981485707082731225149 103451243057140156024209431)
            ·
              refine ⟨155176864585710234036314147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103451243057140156024209431 155176864585710234036314147)
              ·
                refine ⟨232765296878565351054471221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155176864585710234036314147 232765296878565351054471221)
                ·
                  refine ⟨21821746582365501661356677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 232765296878565351054471221 21821746582365501661356677)
                  ·
                    refine ⟨4091577484193531561504377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21821746582365501661356677 4091577484193531561504377)
                    ·
                      refine ⟨3068683113145148671128283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4091577484193531561504377 3068683113145148671128283)
                      ·
                        rfl

theorem cell23_5976239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 4, 2].length) (baseStart_5976239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976239 prefixEnd_5976239 := by exact prefixLift 5976239
  have htrace : WordTrace (prefixWord ++ tailWord_5976239) baseStart_5976239 baseEnd_5976239 := by
    simpa [prefixWord, tailWord_5976239, baseEnd_5976239] using wordTrace_append hprefix tailTrace_5976239
  have hstable : (prefixWord ++ tailWord_5976239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976239).length < 2 ^ (prefixWord ++ tailWord_5976239).sum := by decide
  have hdescent : baseEnd_5976239 < baseStart_5976239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976256 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 1, 4, 2]
def baseStart_5976256 : Nat := 118140960795 + 5976256 * 2 ^ 59
def prefixEnd_5976256 : Nat := 4983230072969 + 3 ^ 40 * 5976256 * 2
def baseEnd_5976256 : Nat := 3068691842316275104615705

theorem tailTrace_5976256 : CollatzResearch.WordTrace tailWord_5976256 prefixEnd_5976256 3068691842316275104615705 := by
  unfold tailWord_5976256
  simp only [CollatzResearch.WordTrace]
  refine ⟨108985981718526325055378311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145314642291368433407171081 108985981718526325055378311)
  ·
    refine ⟨163478972577789487583067467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108985981718526325055378311 163478972577789487583067467)
    ·
      refine ⟨245218458866684231374601201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163478972577789487583067467 245218458866684231374601201)
      ·
        refine ⟨183913844150013173530950901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245218458866684231374601201 183913844150013173530950901)
        ·
          refine ⟨17241922889063735018526647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183913844150013173530950901 17241922889063735018526647)
          ·
            refine ⟨25862884333595602527789971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17241922889063735018526647 25862884333595602527789971)
            ·
              refine ⟨38794326500393403791684957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25862884333595602527789971 38794326500393403791684957)
              ·
                refine ⟨14547872437647526421881859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38794326500393403791684957 14547872437647526421881859)
                ·
                  refine ⟨21821808656471289632822789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14547872437647526421881859 21821808656471289632822789)
                  ·
                    refine ⟨4091589123088366806154273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21821808656471289632822789 4091589123088366806154273)
                    ·
                      refine ⟨3068691842316275104615705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4091589123088366806154273 3068691842316275104615705)
                      ·
                        rfl

theorem cell23_5976256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 1, 4, 2].length) (baseStart_5976256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976256 prefixEnd_5976256 := by exact prefixLift 5976256
  have htrace : WordTrace (prefixWord ++ tailWord_5976256) baseStart_5976256 baseEnd_5976256 := by
    simpa [prefixWord, tailWord_5976256, baseEnd_5976256] using wordTrace_append hprefix tailTrace_5976256
  have hstable : (prefixWord ++ tailWord_5976256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976256).length < 2 ^ (prefixWord ++ tailWord_5976256).sum := by decide
  have hdescent : baseEnd_5976256 < baseStart_5976256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976277 : List Nat := [1, 3, 2, 4, 2, 2, 2, 1, 1, 3, 2]
def baseStart_5976277 : Nat := 118140960795 + 5976277 * 2 ^ 59
def prefixEnd_5976277 : Nat := 4983230072969 + 3 ^ 40 * 5976277 * 2
def baseEnd_5976277 : Nat := 3068702625410019522453109

theorem tailTrace_5976277 : CollatzResearch.WordTrace tailWord_5976277 prefixEnd_5976277 3068702625410019522453109 := by
  unfold tailWord_5976277
  simp only [CollatzResearch.WordTrace]
  refine ⟨217972729369976570697271085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145315152913317713798180723 217972729369976570697271085)
  ·
    refine ⟨81739773513741214011476657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217972729369976570697271085 81739773513741214011476657)
    ·
      refine ⟨61304830135305910508607493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81739773513741214011476657 61304830135305910508607493)
      ·
        refine ⟨11494655650369858220363905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61304830135305910508607493 11494655650369858220363905)
        ·
          refine ⟨8620991737777393665272929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11494655650369858220363905 8620991737777393665272929)
          ·
            refine ⟨6465743803333045248954697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8620991737777393665272929 6465743803333045248954697)
            ·
              refine ⟨4849307852499783936716023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6465743803333045248954697 4849307852499783936716023)
              ·
                refine ⟨7273961778749675905074035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4849307852499783936716023 7273961778749675905074035)
                ·
                  refine ⟨10910942668124513857611053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7273961778749675905074035 10910942668124513857611053)
                  ·
                    refine ⟨4091603500546692696604145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10910942668124513857611053 4091603500546692696604145)
                    ·
                      refine ⟨3068702625410019522453109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4091603500546692696604145 3068702625410019522453109)
                      ·
                        rfl

theorem cell23_5976277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_5976277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976277 prefixEnd_5976277 := by exact prefixLift 5976277
  have htrace : WordTrace (prefixWord ++ tailWord_5976277) baseStart_5976277 baseEnd_5976277 := by
    simpa [prefixWord, tailWord_5976277, baseEnd_5976277] using wordTrace_append hprefix tailTrace_5976277
  have hstable : (prefixWord ++ tailWord_5976277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976277).length < 2 ^ (prefixWord ++ tailWord_5976277).sum := by decide
  have hdescent : baseEnd_5976277 < baseStart_5976277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976284 : List Nat := [2, 2, 5, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_5976284 : Nat := 118140960795 + 5976284 * 2 ^ 59
def prefixEnd_5976284 : Nat := 4983230072969 + 3 ^ 40 * 5976284 * 2
def baseEnd_5976284 : Nat := 3068706219774600995065577

theorem tailTrace_5976284 : CollatzResearch.WordTrace tailWord_5976284 prefixEnd_5976284 3068706219774600995065577 := by
  unfold tailWord_5976284
  simp only [CollatzResearch.WordTrace]
  refine ⟨108986492340475605446387953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145315323120634140595183937 108986492340475605446387953)
  ·
    refine ⟨81739869255356704084790965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108986492340475605446387953 81739869255356704084790965)
    ·
      refine ⟨7663112742689691007949153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81739869255356704084790965 7663112742689691007949153)
      ·
        refine ⟨5747334557017268255961865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7663112742689691007949153 5747334557017268255961865)
        ·
          refine ⟨4310500917762951191971399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5747334557017268255961865 4310500917762951191971399)
          ·
            refine ⟨6465751376644426787957099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4310500917762951191971399 6465751376644426787957099)
            ·
              refine ⟨9698627064966640181935649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6465751376644426787957099 9698627064966640181935649)
              ·
                refine ⟨7273970298724980136451737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9698627064966640181935649 7273970298724980136451737)
                ·
                  refine ⟨5455477724043735102338803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7273970298724980136451737 5455477724043735102338803)
                  ·
                    refine ⟨8183216586065602653508205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5455477724043735102338803 8183216586065602653508205)
                    ·
                      refine ⟨3068706219774600995065577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8183216586065602653508205 3068706219774600995065577)
                      ·
                        rfl

theorem cell23_5976284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_5976284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976284 prefixEnd_5976284 := by exact prefixLift 5976284
  have htrace : WordTrace (prefixWord ++ tailWord_5976284) baseStart_5976284 baseEnd_5976284 := by
    simpa [prefixWord, tailWord_5976284, baseEnd_5976284] using wordTrace_append hprefix tailTrace_5976284
  have hstable : (prefixWord ++ tailWord_5976284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976284).length < 2 ^ (prefixWord ++ tailWord_5976284).sum := by decide
  have hdescent : baseEnd_5976284 < baseStart_5976284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976289 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 4, 3, 3]
def baseStart_5976289 : Nat := 118140960795 + 5976289 * 2 ^ 59
def prefixEnd_5976289 : Nat := 4983230072969 + 3 ^ 40 * 5976289 * 2
def baseEnd_5976289 : Nat := 3068708787177873475503053

theorem tailTrace_5976289 : CollatzResearch.WordTrace tailWord_5976289 prefixEnd_5976289 3068708787177873475503053 := by
  unfold tailWord_5976289
  simp only [CollatzResearch.WordTrace]
  refine ⟨217973167045933096746707921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145315444697288731164471947 217973167045933096746707921)
  ·
    refine ⟨163479875284449822560030941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217973167045933096746707921 163479875284449822560030941)
    ·
      refine ⟨61304953231668683460011603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163479875284449822560030941 61304953231668683460011603)
      ·
        refine ⟨91957429847503025190017405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61304953231668683460011603 91957429847503025190017405)
        ·
          refine ⟨34484036192813634446256527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91957429847503025190017405 34484036192813634446256527)
          ·
            refine ⟨51726054289220451669384791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34484036192813634446256527 51726054289220451669384791)
            ·
              refine ⟨77589081433830677504077187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51726054289220451669384791 77589081433830677504077187)
              ·
                refine ⟨116383622150746016256115781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77589081433830677504077187 116383622150746016256115781)
                ·
                  refine ⟨21821929153264878048021709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116383622150746016256115781 21821929153264878048021709)
                  ·
                    refine ⟨8183223432474329268008141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21821929153264878048021709 8183223432474329268008141)
                    ·
                      refine ⟨3068708787177873475503053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8183223432474329268008141 3068708787177873475503053)
                      ·
                        rfl

theorem cell23_5976289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_5976289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976289 prefixEnd_5976289 := by exact prefixLift 5976289
  have htrace : WordTrace (prefixWord ++ tailWord_5976289) baseStart_5976289 baseEnd_5976289 := by
    simpa [prefixWord, tailWord_5976289, baseEnd_5976289] using wordTrace_append hprefix tailTrace_5976289
  have hstable : (prefixWord ++ tailWord_5976289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976289).length < 2 ^ (prefixWord ++ tailWord_5976289).sum := by decide
  have hdescent : baseEnd_5976289 < baseStart_5976289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976296 : List Nat := [2, 1, 4, 1, 2, 2, 2, 4, 5]
def baseStart_5976296 : Nat := 118140960795 + 5976296 * 2 ^ 59
def prefixEnd_5976296 : Nat := 4983230072969 + 3 ^ 40 * 5976296 * 2
def baseEnd_5976296 : Nat := 340968042393606105346169

theorem tailTrace_5976296 : CollatzResearch.WordTrace tailWord_5976296 prefixEnd_5976296 340968042393606105346169 := by
  unfold tailWord_5976296
  simp only [CollatzResearch.WordTrace]
  refine ⟨108986711178453868471106371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145315614904605157961475161 108986711178453868471106371)
  ·
    refine ⟨163480066767680802706659557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108986711178453868471106371 163480066767680802706659557)
    ·
      refine ⟨30652512518940150507498667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163480066767680802706659557 30652512518940150507498667)
      ·
        refine ⟨45978768778410225761248001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30652512518940150507498667 45978768778410225761248001)
        ·
          refine ⟨34484076583807669320936001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45978768778410225761248001 34484076583807669320936001)
          ·
            refine ⟨25863057437855751990702001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34484076583807669320936001 25863057437855751990702001)
            ·
              refine ⟨19397293078391813993026501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25863057437855751990702001 19397293078391813993026501)
              ·
                refine ⟨3636992452198465123692469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19397293078391813993026501 3636992452198465123692469)
                ·
                  refine ⟨340968042393606105346169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3636992452198465123692469 340968042393606105346169)
                  ·
                    rfl

theorem cell23_5976296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 5].length) (baseStart_5976296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976296 prefixEnd_5976296 := by exact prefixLift 5976296
  have htrace : WordTrace (prefixWord ++ tailWord_5976296) baseStart_5976296 baseEnd_5976296 := by
    simpa [prefixWord, tailWord_5976296, baseEnd_5976296] using wordTrace_append hprefix tailTrace_5976296
  have hstable : (prefixWord ++ tailWord_5976296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976296).length < 2 ^ (prefixWord ++ tailWord_5976296).sum := by decide
  have hdescent : baseEnd_5976296 < baseStart_5976296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976306 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 2, 3, 3]
def baseStart_5976306 : Nat := 118140960795 + 5976306 * 2 ^ 59
def prefixEnd_5976306 : Nat := 4983230072969 + 3 ^ 40 * 5976306 * 2
def baseEnd_5976306 : Nat := 3068717516348999908990475

theorem tailTrace_5976306 : CollatzResearch.WordTrace tailWord_5976306 prefixEnd_5976306 3068717516348999908990475 := by
  unfold tailWord_5976306
  simp only [CollatzResearch.WordTrace]
  refine ⟨54493446771717877162519193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145315858057914339100051181 54493446771717877162519193)
  ·
    refine ⟨40870085078788407871889395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54493446771717877162519193 40870085078788407871889395)
    ·
      refine ⟨61305127618182611807834093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40870085078788407871889395 61305127618182611807834093)
      ·
        refine ⟨22989422856818479427937785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61305127618182611807834093 22989422856818479427937785)
        ·
          refine ⟨17242067142613859570953339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22989422856818479427937785 17242067142613859570953339)
          ·
            refine ⟨25863100713920789356430009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17242067142613859570953339 25863100713920789356430009)
            ·
              refine ⟨19397325535440592017322507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25863100713920789356430009 19397325535440592017322507)
              ·
                refine ⟨29095988303160888025983761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19397325535440592017322507 29095988303160888025983761)
                ·
                  refine ⟨21821991227370666019487821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29095988303160888025983761 21821991227370666019487821)
                  ·
                    refine ⟨8183246710263999757307933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21821991227370666019487821 8183246710263999757307933)
                    ·
                      refine ⟨3068717516348999908990475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8183246710263999757307933 3068717516348999908990475)
                      ·
                        rfl

theorem cell23_5976306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_5976306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976306 prefixEnd_5976306 := by exact prefixLift 5976306
  have htrace : WordTrace (prefixWord ++ tailWord_5976306) baseStart_5976306 baseEnd_5976306 := by
    simpa [prefixWord, tailWord_5976306, baseEnd_5976306] using wordTrace_append hprefix tailTrace_5976306
  have hstable : (prefixWord ++ tailWord_5976306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976306).length < 2 ^ (prefixWord ++ tailWord_5976306).sum := by decide
  have hdescent : baseEnd_5976306 < baseStart_5976306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976329 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 1, 3, 4]
def baseStart_5976329 : Nat := 118140960795 + 5976329 * 2 ^ 59
def prefixEnd_5976329 : Nat := 4983230072969 + 3 ^ 40 * 5976329 * 2
def baseEnd_5976329 : Nat := 3068729326404053319002869

theorem tailTrace_5976329 : CollatzResearch.WordTrace tailWord_5976329 prefixEnd_5976329 3068729326404053319002869 := by
  unfold tailWord_5976329
  simp only [CollatzResearch.WordTrace]
  refine ⟨217974625965788183578164041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145316417310525455718776027 217974625965788183578164041)
  ·
    refine ⟨163480969474341137683623031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217974625965788183578164041 163480969474341137683623031)
    ·
      refine ⟨245221454211511706525434547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163480969474341137683623031 245221454211511706525434547)
      ·
        refine ⟨367832181317267559788151821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245221454211511706525434547 367832181317267559788151821)
        ·
          refine ⟨137937067993975334920556933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367832181317267559788151821 137937067993975334920556933)
          ·
            refine ⟨25863200248870375297604425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137937067993975334920556933 25863200248870375297604425)
            ·
              refine ⟨19397400186652781473203319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25863200248870375297604425 19397400186652781473203319)
              ·
                refine ⟨29096100279979172209804979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19397400186652781473203319 29096100279979172209804979)
                ·
                  refine ⟨43644150419968758314707469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29096100279979172209804979 43644150419968758314707469)
                  ·
                    refine ⟨16366556407488284368015301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43644150419968758314707469 16366556407488284368015301)
                    ·
                      refine ⟨3068729326404053319002869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16366556407488284368015301 3068729326404053319002869)
                      ·
                        rfl

theorem cell23_5976329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_5976329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976329 prefixEnd_5976329 := by exact prefixLift 5976329
  have htrace : WordTrace (prefixWord ++ tailWord_5976329) baseStart_5976329 baseEnd_5976329 := by
    simpa [prefixWord, tailWord_5976329, baseEnd_5976329] using wordTrace_append hprefix tailTrace_5976329
  have hstable : (prefixWord ++ tailWord_5976329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976329).length < 2 ^ (prefixWord ++ tailWord_5976329).sum := by decide
  have hdescent : baseEnd_5976329 < baseStart_5976329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976339 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 5, 4]
def baseStart_5976339 : Nat := 118140960795 + 5976339 * 2 ^ 59
def prefixEnd_5976339 : Nat := 4983230072969 + 3 ^ 40 * 5976339 * 2
def baseEnd_5976339 : Nat := 1022911487070199426625941

theorem tailTrace_5976339 : CollatzResearch.WordTrace tailWord_5976339 prefixEnd_5976339 1022911487070199426625941 := by
  unfold tailWord_5976339
  simp only [CollatzResearch.WordTrace]
  refine ⟨217974990695751955286028071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145316660463834636857352047 217974990695751955286028071)
  ·
    refine ⟨326962486043627932929042107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217974990695751955286028071 326962486043627932929042107)
    ·
      refine ⟨490443729065441899393563161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326962486043627932929042107 490443729065441899393563161)
      ·
        refine ⟨367832796799081424545172371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490443729065441899393563161 367832796799081424545172371)
        ·
          refine ⟨551749195198622136817758557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367832796799081424545172371 551749195198622136817758557)
          ·
            refine ⟨206905948199483301306659459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 551749195198622136817758557 206905948199483301306659459)
            ·
              refine ⟨310358922299224951959989189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206905948199483301306659459 310358922299224951959989189)
              ·
                refine ⟨58192297931104678492497973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 310358922299224951959989189 58192297931104678492497973)
                ·
                  refine ⟨5455527931041063608671685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58192297931104678492497973 5455527931041063608671685)
                  ·
                    refine ⟨1022911487070199426625941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5455527931041063608671685 1022911487070199426625941)
                    ·
                      rfl

theorem cell23_5976339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 4].length) (baseStart_5976339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976339 prefixEnd_5976339 := by exact prefixLift 5976339
  have htrace : WordTrace (prefixWord ++ tailWord_5976339) baseStart_5976339 baseEnd_5976339 := by
    simpa [prefixWord, tailWord_5976339, baseEnd_5976339] using wordTrace_append hprefix tailTrace_5976339
  have hstable : (prefixWord ++ tailWord_5976339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976339).length < 2 ^ (prefixWord ++ tailWord_5976339).sum := by decide
  have hdescent : baseEnd_5976339 < baseStart_5976339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976439 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 5]
def baseStart_5976439 : Nat := 118140960795 + 5976439 * 2 ^ 59
def prefixEnd_5976439 : Nat := 4983230072969 + 3 ^ 40 * 5976439 * 2
def baseEnd_5976439 : Nat := 3068785809276047888627363

theorem tailTrace_5976439 : CollatzResearch.WordTrace tailWord_5976439 prefixEnd_5976439 3068785809276047888627363 := by
  unfold tailWord_5976439
  simp only [CollatzResearch.WordTrace]
  refine ⟨217978637995389672364668371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145319091996926448243112247 217978637995389672364668371)
  ·
    refine ⟨326967956993084508547002557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217978637995389672364668371 326967956993084508547002557)
    ·
      refine ⟨122612983872406690705125959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326967956993084508547002557 122612983872406690705125959)
      ·
        refine ⟨183919475808610036057688939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122612983872406690705125959 183919475808610036057688939)
        ·
          refine ⟨275879213712915054086533409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183919475808610036057688939 275879213712915054086533409)
          ·
            refine ⟨206909410284686290564900057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275879213712915054086533409 206909410284686290564900057)
            ·
              refine ⟨155182057713514717923675043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206909410284686290564900057 155182057713514717923675043)
              ·
                refine ⟨232773086570272076885512565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155182057713514717923675043 232773086570272076885512565)
                ·
                  refine ⟨21822476865963007208016803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 232773086570272076885512565 21822476865963007208016803)
                  ·
                    refine ⟨32733715298944510812025205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21822476865963007208016803 32733715298944510812025205)
                    ·
                      refine ⟨3068785809276047888627363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32733715298944510812025205 3068785809276047888627363)
                      ·
                        rfl

theorem cell23_5976439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_5976439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976439 prefixEnd_5976439 := by exact prefixLift 5976439
  have htrace : WordTrace (prefixWord ++ tailWord_5976439) baseStart_5976439 baseEnd_5976439 := by
    simpa [prefixWord, tailWord_5976439, baseEnd_5976439] using wordTrace_append hprefix tailTrace_5976439
  have hstable : (prefixWord ++ tailWord_5976439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976439).length < 2 ^ (prefixWord ++ tailWord_5976439).sum := by decide
  have hdescent : baseEnd_5976439 < baseStart_5976439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976453 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 7, 2, 2]
def baseStart_5976453 : Nat := 118140960795 + 5976453 * 2 ^ 59
def prefixEnd_5976453 : Nat := 4983230072969 + 3 ^ 40 * 5976453 * 2
def baseEnd_5976453 : Nat := 3068792998005210833852299

theorem tailTrace_5976453 : CollatzResearch.WordTrace tailWord_5976453 prefixEnd_5976453 3068792998005210833852299 := by
  unfold tailWord_5976453
  simp only [CollatzResearch.WordTrace]
  refine ⟨217979148617338952755678013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145319432411559301837118675 217979148617338952755678013)
  ·
    refine ⟨81742180731502107283379255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217979148617338952755678013 81742180731502107283379255)
    ·
      refine ⟨122613271097253160925068883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81742180731502107283379255 122613271097253160925068883)
      ·
        refine ⟨183919906645879741387603325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122613271097253160925068883 183919906645879741387603325)
        ·
          refine ⟨68969964992204903020351247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183919906645879741387603325 68969964992204903020351247)
          ·
            refine ⟨103454947488307354530526871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68969964992204903020351247 103454947488307354530526871)
            ·
              refine ⟨155182421232461031795790307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103454947488307354530526871 155182421232461031795790307)
              ·
                refine ⟨232773631848691547693685461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155182421232461031795790307 232773631848691547693685461)
                ·
                  refine ⟨5455631996453708149070753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 232773631848691547693685461 5455631996453708149070753)
                  ·
                    refine ⟨4091723997340281111803065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5455631996453708149070753 4091723997340281111803065)
                    ·
                      refine ⟨3068792998005210833852299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4091723997340281111803065 3068792998005210833852299)
                      ·
                        rfl

theorem cell23_5976453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 2, 2].length) (baseStart_5976453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976453 prefixEnd_5976453 := by exact prefixLift 5976453
  have htrace : WordTrace (prefixWord ++ tailWord_5976453) baseStart_5976453 baseEnd_5976453 := by
    simpa [prefixWord, tailWord_5976453, baseEnd_5976453] using wordTrace_append hprefix tailTrace_5976453
  have hstable : (prefixWord ++ tailWord_5976453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976453).length < 2 ^ (prefixWord ++ tailWord_5976453).sum := by decide
  have hdescent : baseEnd_5976453 < baseStart_5976453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976456 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_5976456 : Nat := 118140960795 + 5976456 * 2 ^ 59
def prefixEnd_5976456 : Nat := 4983230072969 + 3 ^ 40 * 5976456 * 2
def baseEnd_5976456 : Nat := 3068794538447174322114785

theorem tailTrace_5976456 : CollatzResearch.WordTrace tailWord_5976456 prefixEnd_5976456 3068794538447174322114785 := by
  unfold tailWord_5976456
  simp only [CollatzResearch.WordTrace]
  refine ⟨108989629018164042134018611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145319505357552056178691481 108989629018164042134018611)
  ·
    refine ⟨163484443527246063201027917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108989629018164042134018611 163484443527246063201027917)
    ·
      refine ⟨61306666322717273700385469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163484443527246063201027917 61306666322717273700385469)
      ·
        refine ⟨22989999871018977637644551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61306666322717273700385469 22989999871018977637644551)
        ·
          refine ⟨34484999806528466456466827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22989999871018977637644551 34484999806528466456466827)
          ·
            refine ⟨51727499709792699684700241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34484999806528466456466827 51727499709792699684700241)
            ·
              refine ⟨38795624782344524763525181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51727499709792699684700241 38795624782344524763525181)
              ·
                refine ⟨14548359293379196786321943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38795624782344524763525181 14548359293379196786321943)
                ·
                  refine ⟨21822538940068795179482915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14548359293379196786321943 21822538940068795179482915)
                  ·
                    refine ⟨32733808410103192769224373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21822538940068795179482915 32733808410103192769224373)
                    ·
                      refine ⟨3068794538447174322114785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32733808410103192769224373 3068794538447174322114785)
                      ·
                        rfl

theorem cell23_5976456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_5976456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976456 prefixEnd_5976456 := by exact prefixLift 5976456
  have htrace : WordTrace (prefixWord ++ tailWord_5976456) baseStart_5976456 baseEnd_5976456 := by
    simpa [prefixWord, tailWord_5976456, baseEnd_5976456] using wordTrace_append hprefix tailTrace_5976456
  have hstable : (prefixWord ++ tailWord_5976456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976456).length < 2 ^ (prefixWord ++ tailWord_5976456).sum := by decide
  have hdescent : baseEnd_5976456 < baseStart_5976456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976459 : List Nat := [1, 1, 1, 1, 4, 5, 10]
def baseStart_5976459 : Nat := 118140960795 + 5976459 * 2 ^ 59
def prefixEnd_5976459 : Nat := 4983230072969 + 3 ^ 40 * 5976459 * 2
def baseEnd_5976459 : Nat := 37886371344310343337991

theorem tailTrace_5976459 : CollatzResearch.WordTrace tailWord_5976459 prefixEnd_5976459 37886371344310343337991 := by
  unfold tailWord_5976459
  simp only [CollatzResearch.WordTrace]
  refine ⟨217979367455317215780396431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145319578303544810520264287 217979367455317215780396431)
  ·
    refine ⟨326969051182975823670594647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217979367455317215780396431 326969051182975823670594647)
    ·
      refine ⟨490453576774463735505891971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326969051182975823670594647 490453576774463735505891971)
      ·
        refine ⟨735680365161695603258837957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490453576774463735505891971 735680365161695603258837957)
        ·
          refine ⟨137940068467817925611032117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 735680365161695603258837957 137940068467817925611032117)
          ·
            refine ⟨12931881418857930526034261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137940068467817925611032117 12931881418857930526034261)
            ·
              refine ⟨37886371344310343337991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12931881418857930526034261 37886371344310343337991)
              ·
                rfl

theorem cell23_5976459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 10].length) (baseStart_5976459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976459 prefixEnd_5976459 := by exact prefixLift 5976459
  have htrace : WordTrace (prefixWord ++ tailWord_5976459) baseStart_5976459 baseEnd_5976459 := by
    simpa [prefixWord, tailWord_5976459, baseEnd_5976459] using wordTrace_append hprefix tailTrace_5976459
  have hstable : (prefixWord ++ tailWord_5976459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976459).length < 2 ^ (prefixWord ++ tailWord_5976459).sum := by decide
  have hdescent : baseEnd_5976459 < baseStart_5976459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976469 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_5976469 : Nat := 118140960795 + 5976469 * 2 ^ 59
def prefixEnd_5976469 : Nat := 4983230072969 + 3 ^ 40 * 5976469 * 2
def baseEnd_5976469 : Nat := 3068801213695682771252225

theorem tailTrace_5976469 : CollatzResearch.WordTrace tailWord_5976469 prefixEnd_5976469 3068801213695682771252225 := by
  unfold tailWord_5976469
  simp only [CollatzResearch.WordTrace]
  refine ⟨217979732185280987488260461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145319821456853991658840307 217979732185280987488260461)
  ·
    refine ⟨81742399569480370308097673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217979732185280987488260461 81742399569480370308097673)
    ·
      refine ⟨61306799677110277731073255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81742399569480370308097673 61306799677110277731073255)
      ·
        refine ⟨91960199515665416596609883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61306799677110277731073255 91960199515665416596609883)
        ·
          refine ⟨137940299273498124894914825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91960199515665416596609883 137940299273498124894914825)
          ·
            refine ⟨103455224455123593671186119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137940299273498124894914825 103455224455123593671186119)
            ·
              refine ⟨155182836682685390506779179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103455224455123593671186119 155182836682685390506779179)
              ·
                refine ⟨232774255024028085760168769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155182836682685390506779179 232774255024028085760168769)
                ·
                  refine ⟨174580691268021064320126577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232774255024028085760168769 174580691268021064320126577)
                  ·
                    refine ⟨130935518451015798240094933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 174580691268021064320126577 130935518451015798240094933)
                    ·
                      refine ⟨3068801213695682771252225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130935518451015798240094933 3068801213695682771252225)
                      ·
                        rfl

theorem cell23_5976469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_5976469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976469 prefixEnd_5976469 := by exact prefixLift 5976469
  have htrace : WordTrace (prefixWord ++ tailWord_5976469) baseStart_5976469 baseEnd_5976469 := by
    simpa [prefixWord, tailWord_5976469, baseEnd_5976469] using wordTrace_append hprefix tailTrace_5976469
  have hstable : (prefixWord ++ tailWord_5976469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976469).length < 2 ^ (prefixWord ++ tailWord_5976469).sum := by decide
  have hdescent : baseEnd_5976469 < baseStart_5976469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976480 : List Nat := [2, 1, 1, 4, 1, 4, 3, 1, 2, 4]
def baseStart_5976480 : Nat := 118140960795 + 5976480 * 2 ^ 59
def prefixEnd_5976480 : Nat := 4983230072969 + 3 ^ 40 * 5976480 * 2
def baseEnd_5976480 : Nat := 1022935620660960742738225

theorem tailTrace_5976480 : CollatzResearch.WordTrace tailWord_5976480 prefixEnd_5976480 1022935620660960742738225 := by
  unfold tailWord_5976480
  simp only [CollatzResearch.WordTrace]
  refine ⟨108990066694120568183455447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145320088925494090911273929 108990066694120568183455447)
  ·
    refine ⟨163485100041180852275183171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108990066694120568183455447 163485100041180852275183171)
    ·
      refine ⟨245227650061771278412774757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163485100041180852275183171 245227650061771278412774757)
      ·
        refine ⟨45980184386582114702395267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245227650061771278412774757 45980184386582114702395267)
        ·
          refine ⟨68970276579873172053592901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45980184386582114702395267 68970276579873172053592901)
          ·
            refine ⟨12931926858726219760048669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68970276579873172053592901 12931926858726219760048669)
            ·
              refine ⟨4849472572022332410018251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12931926858726219760048669 4849472572022332410018251)
              ·
                refine ⟨7274208858033498615027377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4849472572022332410018251 7274208858033498615027377)
                ·
                  refine ⟨5455656643525123961270533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7274208858033498615027377 5455656643525123961270533)
                  ·
                    refine ⟨1022935620660960742738225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5455656643525123961270533 1022935620660960742738225)
                    ·
                      rfl

theorem cell23_5976480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 2, 4].length) (baseStart_5976480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976480 prefixEnd_5976480 := by exact prefixLift 5976480
  have htrace : WordTrace (prefixWord ++ tailWord_5976480) baseStart_5976480 baseEnd_5976480 := by
    simpa [prefixWord, tailWord_5976480, baseEnd_5976480] using wordTrace_append hprefix tailTrace_5976480
  have hstable : (prefixWord ++ tailWord_5976480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976480).length < 2 ^ (prefixWord ++ tailWord_5976480).sum := by decide
  have hdescent : baseEnd_5976480 < baseStart_5976480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976483 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 1, 2, 4]
def baseStart_5976483 : Nat := 118140960795 + 5976483 * 2 ^ 59
def prefixEnd_5976483 : Nat := 4983230072969 + 3 ^ 40 * 5976483 * 2
def baseEnd_5976483 : Nat := 3068808402424845716477161

theorem tailTrace_5976483 : CollatzResearch.WordTrace tailWord_5976483 prefixEnd_5976483 3068808402424845716477161 := by
  unfold tailWord_5976483
  simp only [CollatzResearch.WordTrace]
  refine ⟨217980242807230267879270103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145320161871486845252846735 217980242807230267879270103)
  ·
    refine ⟨326970364210845401818905155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217980242807230267879270103 326970364210845401818905155)
    ·
      refine ⟨490455546316268102728357733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326970364210845401818905155 490455546316268102728357733)
      ·
        refine ⟨91960414934300269261567075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 490455546316268102728357733 91960414934300269261567075)
        ·
          refine ⟨137940622401450403892350613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91960414934300269261567075 137940622401450403892350613)
          ·
            refine ⟨6465966675067987682453935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 137940622401450403892350613 6465966675067987682453935)
            ·
              refine ⟨9698950012601981523680903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6465966675067987682453935 9698950012601981523680903)
              ·
                refine ⟨14548425018902972285521355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9698950012601981523680903 14548425018902972285521355)
                ·
                  refine ⟨21822637528354458428282033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14548425018902972285521355 21822637528354458428282033)
                  ·
                    refine ⟨16366978146265843821211525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21822637528354458428282033 16366978146265843821211525)
                    ·
                      refine ⟨3068808402424845716477161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16366978146265843821211525 3068808402424845716477161)
                      ·
                        rfl

theorem cell23_5976483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_5976483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976483 prefixEnd_5976483 := by exact prefixLift 5976483
  have htrace : WordTrace (prefixWord ++ tailWord_5976483) baseStart_5976483 baseEnd_5976483 := by
    simpa [prefixWord, tailWord_5976483, baseEnd_5976483] using wordTrace_append hprefix tailTrace_5976483
  have hstable : (prefixWord ++ tailWord_5976483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976483).length < 2 ^ (prefixWord ++ tailWord_5976483).sum := by decide
  have hdescent : baseEnd_5976483 < baseStart_5976483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976489 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 2, 7]
def baseStart_5976489 : Nat := 118140960795 + 5976489 * 2 ^ 59
def prefixEnd_5976489 : Nat := 4983230072969 + 3 ^ 40 * 5976489 * 2
def baseEnd_5976489 : Nat := 1022937161102924231000711

theorem tailTrace_5976489 : CollatzResearch.WordTrace tailWord_5976489 prefixEnd_5976489 1022937161102924231000711 := by
  unfold tailWord_5976489
  simp only [CollatzResearch.WordTrace]
  refine ⟨217980461645208530903988521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145320307763472353935992347 217980461645208530903988521)
  ·
    refine ⟨163485346233906398177991391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217980461645208530903988521 163485346233906398177991391)
    ·
      refine ⟨245228019350859597266987087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163485346233906398177991391 245228019350859597266987087)
      ·
        refine ⟨367842029026289395900480631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245228019350859597266987087 367842029026289395900480631)
        ·
          refine ⟨551763043539434093850720947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367842029026289395900480631 551763043539434093850720947)
          ·
            refine ⟨827644565309151140776081421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551763043539434093850720947 827644565309151140776081421)
            ·
              refine ⟨310366711990931677791030533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 827644565309151140776081421 310366711990931677791030533)
              ·
                refine ⟨58193758498299689585818225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 310366711990931677791030533 58193758498299689585818225)
                ·
                  refine ⟨43645318873724767189363669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58193758498299689585818225 43645318873724767189363669)
                  ·
                    refine ⟨1022937161102924231000711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43645318873724767189363669 1022937161102924231000711)
                    ·
                      rfl

theorem cell23_5976489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 7].length) (baseStart_5976489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976489 prefixEnd_5976489 := by exact prefixLift 5976489
  have htrace : WordTrace (prefixWord ++ tailWord_5976489) baseStart_5976489 baseEnd_5976489 := by
    simpa [prefixWord, tailWord_5976489, baseEnd_5976489] using wordTrace_append hprefix tailTrace_5976489
  have hstable : (prefixWord ++ tailWord_5976489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976489).length < 2 ^ (prefixWord ++ tailWord_5976489).sum := by decide
  have hdescent : baseEnd_5976489 < baseStart_5976489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976493 : List Nat := [1, 5, 2, 2, 2, 1, 1, 9]
def baseStart_5976493 : Nat := 118140960795 + 5976493 * 2 ^ 59
def prefixEnd_5976493 : Nat := 4983230072969 + 3 ^ 40 * 5976493 * 2
def baseEnd_5976493 : Nat := 113659760638199654716745

theorem tailTrace_5976493 : CollatzResearch.WordTrace tailWord_5976493 prefixEnd_5976493 113659760638199654716745 := by
  unfold tailWord_5976493
  simp only [CollatzResearch.WordTrace]
  refine ⟨217980607537194039587134133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145320405024796026391422755 217980607537194039587134133)
  ·
    refine ⟨20435681956611941211293825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217980607537194039587134133 20435681956611941211293825)
    ·
      refine ⟨15326761467458955908470369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20435681956611941211293825 15326761467458955908470369)
      ·
        refine ⟨11495071100594216931352777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15326761467458955908470369 11495071100594216931352777)
        ·
          refine ⟨8621303325445662698514583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11495071100594216931352777 8621303325445662698514583)
          ·
            refine ⟨12931954988168494047771875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8621303325445662698514583 12931954988168494047771875)
            ·
              refine ⟨19397932482252741071657813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12931954988168494047771875 19397932482252741071657813)
              ·
                refine ⟨113659760638199654716745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19397932482252741071657813 113659760638199654716745)
                ·
                  rfl

theorem cell23_5976493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 9].length) (baseStart_5976493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976493 prefixEnd_5976493 := by exact prefixLift 5976493
  have htrace : WordTrace (prefixWord ++ tailWord_5976493) baseStart_5976493 baseEnd_5976493 := by
    simpa [prefixWord, tailWord_5976493, baseEnd_5976493] using wordTrace_append hprefix tailTrace_5976493
  have hstable : (prefixWord ++ tailWord_5976493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976493).length < 2 ^ (prefixWord ++ tailWord_5976493).sum := by decide
  have hdescent : baseEnd_5976493 < baseStart_5976493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976503 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 4, 1, 3]
def baseStart_5976503 : Nat := 118140960795 + 5976503 * 2 ^ 59
def prefixEnd_5976503 : Nat := 4983230072969 + 3 ^ 40 * 5976503 * 2
def baseEnd_5976503 : Nat := 3068818672037935638227069

theorem tailTrace_5976503 : CollatzResearch.WordTrace tailWord_5976503 prefixEnd_5976503 3068818672037935638227069 := by
  unfold tailWord_5976503
  simp only [CollatzResearch.WordTrace]
  refine ⟨217980972267157811294998163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145320648178105207529998775 217980972267157811294998163)
  ·
    refine ⟨326971458400736716942497245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217980972267157811294998163 326971458400736716942497245)
    ·
      refine ⟨122614296900276268853436467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326971458400736716942497245 122614296900276268853436467)
      ·
        refine ⟨183921445350414403280154701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122614296900276268853436467 183921445350414403280154701)
        ·
          refine ⟨68970542006405401230058013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183921445350414403280154701 68970542006405401230058013)
          ·
            refine ⟨25863953252402025461271755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68970542006405401230058013 25863953252402025461271755)
            ·
              refine ⟨38795929878603038191907633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25863953252402025461271755 38795929878603038191907633)
              ·
                refine ⟨29096947408952278643930725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38795929878603038191907633 29096947408952278643930725)
                ·
                  refine ⟨5455677639178552245737011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29096947408952278643930725 5455677639178552245737011)
                  ·
                    refine ⟨8183516458767828368605517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5455677639178552245737011 8183516458767828368605517)
                    ·
                      refine ⟨3068818672037935638227069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8183516458767828368605517 3068818672037935638227069)
                      ·
                        rfl

theorem cell23_5976503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 1, 3].length) (baseStart_5976503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976503 prefixEnd_5976503 := by exact prefixLift 5976503
  have htrace : WordTrace (prefixWord ++ tailWord_5976503) baseStart_5976503 baseEnd_5976503 := by
    simpa [prefixWord, tailWord_5976503, baseEnd_5976503] using wordTrace_append hprefix tailTrace_5976503
  have hstable : (prefixWord ++ tailWord_5976503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976503).length < 2 ^ (prefixWord ++ tailWord_5976503).sum := by decide
  have hdescent : baseEnd_5976503 < baseStart_5976503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976526 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_5976526 : Nat := 118140960795 + 5976526 * 2 ^ 59
def prefixEnd_5976526 : Nat := 4983230072969 + 3 ^ 40 * 5976526 * 2
def baseEnd_5976526 : Nat := 3068830482092989048239463

theorem tailTrace_5976526 : CollatzResearch.WordTrace tailWord_5976526 prefixEnd_5976526 3068830482092989048239463 := by
  unfold tailWord_5976526
  simp only [CollatzResearch.WordTrace]
  refine ⟨27247726393259310777885679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145321207430716324148723621 27247726393259310777885679)
  ·
    refine ⟨40871589589888966166828519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27247726393259310777885679 40871589589888966166828519)
    ·
      refine ⟨61307384384833449250242779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40871589589888966166828519 61307384384833449250242779)
      ·
        refine ⟨91961076577250173875364169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61307384384833449250242779 91961076577250173875364169)
        ·
          refine ⟨68970807432937630406523127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91961076577250173875364169 68970807432937630406523127)
          ·
            refine ⟨103456211149406445609784691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68970807432937630406523127 103456211149406445609784691)
            ·
              refine ⟨155184316724109668414677037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103456211149406445609784691 155184316724109668414677037)
              ·
                refine ⟨58194118771541125655503889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155184316724109668414677037 58194118771541125655503889)
                ·
                  refine ⟨43645589078655844241627917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58194118771541125655503889 43645589078655844241627917)
                  ·
                    refine ⟨16367095904495941590610469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43645589078655844241627917 16367095904495941590610469)
                    ·
                      refine ⟨3068830482092989048239463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16367095904495941590610469 3068830482092989048239463)
                      ·
                        rfl

theorem cell23_5976526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_5976526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976526 prefixEnd_5976526 := by exact prefixLift 5976526
  have htrace : WordTrace (prefixWord ++ tailWord_5976526) baseStart_5976526 baseEnd_5976526 := by
    simpa [prefixWord, tailWord_5976526, baseEnd_5976526] using wordTrace_append hprefix tailTrace_5976526
  have hstable : (prefixWord ++ tailWord_5976526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976526).length < 2 ^ (prefixWord ++ tailWord_5976526).sum := by decide
  have hdescent : baseEnd_5976526 < baseStart_5976526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976576 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 3]
def baseStart_5976576 : Nat := 118140960795 + 5976576 * 2 ^ 59
def prefixEnd_5976576 : Nat := 4983230072969 + 3 ^ 40 * 5976576 * 2
def baseEnd_5976576 : Nat := 3068856156125713852614233

theorem tailTrace_5976576 : CollatzResearch.WordTrace tailWord_5976576 prefixEnd_5976576 3068856156125713852614233 := by
  unfold tailWord_5976576
  simp only [CollatzResearch.WordTrace]
  refine ⟨108991817397946672381202791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145322423197262229841603721 108991817397946672381202791)
  ·
    refine ⟨163487726096920008571804187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108991817397946672381202791 163487726096920008571804187)
    ·
      refine ⟨245231589145380012857706281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163487726096920008571804187 245231589145380012857706281)
      ·
        refine ⟨183923691859035009643279711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245231589145380012857706281 183923691859035009643279711)
        ·
          refine ⟨275885537788552514464919567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183923691859035009643279711 275885537788552514464919567)
          ·
            refine ⟨413828306682828771697379351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275885537788552514464919567 413828306682828771697379351)
            ·
              refine ⟨620742460024243157546069027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413828306682828771697379351 620742460024243157546069027)
              ·
                refine ⟨931113690036364736319103541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620742460024243157546069027 931113690036364736319103541)
                ·
                  refine ⟨87291908440909194029915957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 931113690036364736319103541 87291908440909194029915957)
                  ·
                    refine ⟨8183616416335236940304621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87291908440909194029915957 8183616416335236940304621)
                    ·
                      refine ⟨3068856156125713852614233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8183616416335236940304621 3068856156125713852614233)
                      ·
                        rfl

theorem cell23_5976576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_5976576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976576 prefixEnd_5976576 := by exact prefixLift 5976576
  have htrace : WordTrace (prefixWord ++ tailWord_5976576) baseStart_5976576 baseEnd_5976576 := by
    simpa [prefixWord, tailWord_5976576, baseEnd_5976576] using wordTrace_append hprefix tailTrace_5976576
  have hstable : (prefixWord ++ tailWord_5976576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976576).length < 2 ^ (prefixWord ++ tailWord_5976576).sum := by decide
  have hdescent : baseEnd_5976576 < baseStart_5976576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976577 : List Nat := [1, 2, 4, 1, 3, 1, 1, 4, 2, 2, 2]
def baseStart_5976577 : Nat := 118140960795 + 5976577 * 2 ^ 59
def prefixEnd_5976577 : Nat := 4983230072969 + 3 ^ 40 * 5976577 * 2
def baseEnd_5976577 : Nat := 3068856669606368348701729

theorem tailTrace_5976577 : CollatzResearch.WordTrace tailWord_5976577 prefixEnd_5976577 3068856669606368348701729 := by
  unfold tailWord_5976577
  simp only [CollatzResearch.WordTrace]
  refine ⟨217983671268889721933191985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145322447512593147955461323 217983671268889721933191985)
  ·
    refine ⟨163487753451667291449893989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217983671268889721933191985 163487753451667291449893989)
    ·
      refine ⟨30653953772187617146855123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163487753451667291449893989 30653953772187617146855123)
      ·
        refine ⟨45980930658281425720282685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30653953772187617146855123 45980930658281425720282685)
        ·
          refine ⟨17242848996855534645106007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45980930658281425720282685 17242848996855534645106007)
          ·
            refine ⟨25864273495283301967659011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17242848996855534645106007 25864273495283301967659011)
            ·
              refine ⟨38796410242924952951488517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25864273495283301967659011 38796410242924952951488517)
              ·
                refine ⟨7274326920548428678404097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38796410242924952951488517 7274326920548428678404097)
                ·
                  refine ⟨5455745190411321508803073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7274326920548428678404097 5455745190411321508803073)
                  ·
                    refine ⟨4091808892808491131602305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5455745190411321508803073 4091808892808491131602305)
                    ·
                      refine ⟨3068856669606368348701729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4091808892808491131602305 3068856669606368348701729)
                      ·
                        rfl

theorem cell23_5976577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_5976577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976577 prefixEnd_5976577 := by exact prefixLift 5976577
  have htrace : WordTrace (prefixWord ++ tailWord_5976577) baseStart_5976577 baseEnd_5976577 := by
    simpa [prefixWord, tailWord_5976577, baseEnd_5976577] using wordTrace_append hprefix tailTrace_5976577
  have hstable : (prefixWord ++ tailWord_5976577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976577).length < 2 ^ (prefixWord ++ tailWord_5976577).sum := by decide
  have hdescent : baseEnd_5976577 < baseStart_5976577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976613 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 2, 5]
def baseStart_5976613 : Nat := 118140960795 + 5976613 * 2 ^ 59
def prefixEnd_5976613 : Nat := 4983230072969 + 3 ^ 40 * 5976613 * 2
def baseEnd_5976613 : Nat := 1022958384969976735950521

theorem tailTrace_5976613 : CollatzResearch.WordTrace tailWord_5976613 prefixEnd_5976613 1022958384969976735950521 := by
  unfold tailWord_5976613
  simp only [CollatzResearch.WordTrace]
  refine ⟨217984984296759300081502493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145323322864506200054334995 217984984296759300081502493)
  ·
    refine ⟨81744369111284737530563435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217984984296759300081502493 81744369111284737530563435)
    ·
      refine ⟨122616553666927106295845153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81744369111284737530563435 122616553666927106295845153)
      ·
        refine ⟨91962415250195329721883865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122616553666927106295845153 91962415250195329721883865)
        ·
          refine ⟨68971811437646497291412899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91962415250195329721883865 68971811437646497291412899)
          ·
            refine ⟨103457717156469745937119349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68971811437646497291412899 103457717156469745937119349)
            ·
              refine ⟨9699160983419038681604939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103457717156469745937119349 9699160983419038681604939)
              ·
                refine ⟨14548741475128558022407409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9699160983419038681604939 14548741475128558022407409)
                ·
                  refine ⟨10911556106346418516805557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14548741475128558022407409 10911556106346418516805557)
                  ·
                    refine ⟨1022958384969976735950521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10911556106346418516805557 1022958384969976735950521)
                    ·
                      rfl

theorem cell23_5976613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_5976613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976613 prefixEnd_5976613 := by exact prefixLift 5976613
  have htrace : WordTrace (prefixWord ++ tailWord_5976613) baseStart_5976613 baseEnd_5976613 := by
    simpa [prefixWord, tailWord_5976613, baseEnd_5976613] using wordTrace_append hprefix tailTrace_5976613
  have hstable : (prefixWord ++ tailWord_5976613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976613).length < 2 ^ (prefixWord ++ tailWord_5976613).sum := by decide
  have hdescent : baseEnd_5976613 < baseStart_5976613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976628 : List Nat := [2, 5, 1, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_5976628 : Nat := 118140960795 + 5976628 * 2 ^ 59
def prefixEnd_5976628 : Nat := 4983230072969 + 3 ^ 40 * 5976628 * 2
def baseEnd_5976628 : Nat := 3068882857119747649163995

theorem tailTrace_5976628 : CollatzResearch.WordTrace tailWord_5976628 prefixEnd_5976628 3068882857119747649163995 := by
  unfold tailWord_5976628
  simp only [CollatzResearch.WordTrace]
  refine ⟨108992765695852478821649269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145323687594469971762199025 108992765695852478821649269)
  ·
    refine ⟨10218071783986169889529619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108992765695852478821649269 10218071783986169889529619)
    ·
      refine ⟨15327107675979254834294429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10218071783986169889529619 15327107675979254834294429)
      ·
        refine ⟨5747665378492220562860411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15327107675979254834294429 5747665378492220562860411)
        ·
          refine ⟨8621498067738330844290617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5747665378492220562860411 8621498067738330844290617)
          ·
            refine ⟨6466123550803748133217963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8621498067738330844290617 6466123550803748133217963)
            ·
              refine ⟨9699185326205622199826945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6466123550803748133217963 9699185326205622199826945)
              ·
                refine ⟨7274388994654216649870209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9699185326205622199826945 7274388994654216649870209)
                ·
                  refine ⟨5455791745990662487402657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7274388994654216649870209 5455791745990662487402657)
                  ·
                    refine ⟨4091843809492996865551993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5455791745990662487402657 4091843809492996865551993)
                    ·
                      refine ⟨3068882857119747649163995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4091843809492996865551993 3068882857119747649163995)
                      ·
                        rfl

theorem cell23_5976628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_5976628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976628 prefixEnd_5976628 := by exact prefixLift 5976628
  have htrace : WordTrace (prefixWord ++ tailWord_5976628) baseStart_5976628 baseEnd_5976628 := by
    simpa [prefixWord, tailWord_5976628, baseEnd_5976628] using wordTrace_append hprefix tailTrace_5976628
  have hstable : (prefixWord ++ tailWord_5976628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976628).length < 2 ^ (prefixWord ++ tailWord_5976628).sum := by decide
  have hdescent : baseEnd_5976628 < baseStart_5976628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976633 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 4, 1, 4]
def baseStart_5976633 : Nat := 118140960795 + 5976633 * 2 ^ 59
def prefixEnd_5976633 : Nat := 4983230072969 + 3 ^ 40 * 5976633 * 2
def baseEnd_5976633 : Nat := 3068885424523020129601471

theorem tailTrace_5976633 : CollatzResearch.WordTrace tailWord_5976633 prefixEnd_5976633 3068885424523020129601471 := by
  unfold tailWord_5976633
  simp only [CollatzResearch.WordTrace]
  refine ⟨217985713756686843497230553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145323809171124562331487035 217985713756686843497230553)
  ·
    refine ⟨163489285317515132622922915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217985713756686843497230553 163489285317515132622922915)
    ·
      refine ⟨245233927976272698934384373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163489285317515132622922915 245233927976272698934384373)
      ·
        refine ⟨22990680747775565525098535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 245233927976272698934384373 22990680747775565525098535)
        ·
          refine ⟨34486021121663348287647803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22990680747775565525098535 34486021121663348287647803)
          ·
            refine ⟨51729031682495022431471705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34486021121663348287647803 51729031682495022431471705)
            ·
              refine ⟨38796773761871266823603779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51729031682495022431471705 38796773761871266823603779)
              ·
                refine ⟨58195160642806900235405669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38796773761871266823603779 58195160642806900235405669)
                ·
                  refine ⟨10911592620526293794138563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58195160642806900235405669 10911592620526293794138563)
                  ·
                    refine ⟨16367388930789440691207845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10911592620526293794138563 16367388930789440691207845)
                    ·
                      refine ⟨3068885424523020129601471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16367388930789440691207845 3068885424523020129601471)
                      ·
                        rfl

theorem cell23_5976633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_5976633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976633 prefixEnd_5976633 := by exact prefixLift 5976633
  have htrace : WordTrace (prefixWord ++ tailWord_5976633) baseStart_5976633 baseEnd_5976633 := by
    simpa [prefixWord, tailWord_5976633, baseEnd_5976633] using wordTrace_append hprefix tailTrace_5976633
  have hstable : (prefixWord ++ tailWord_5976633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976633).length < 2 ^ (prefixWord ++ tailWord_5976633).sum := by decide
  have hdescent : baseEnd_5976633 < baseStart_5976633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976650 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 2, 4, 2]
def baseStart_5976650 : Nat := 118140960795 + 5976650 * 2 ^ 59
def prefixEnd_5976650 : Nat := 4983230072969 + 3 ^ 40 * 5976650 * 2
def baseEnd_5976650 : Nat := 3068894153694146563088893

theorem tailTrace_5976650 : CollatzResearch.WordTrace tailWord_5976650 prefixEnd_5976650 3068894153694146563088893 := by
  unfold tailWord_5976650
  simp only [CollatzResearch.WordTrace]
  refine ⟨54496583449406313850149851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145324222531750170267066269 54496583449406313850149851)
  ·
    refine ⟨81744875174109470775224777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54496583449406313850149851 81744875174109470775224777)
    ·
      refine ⟨61308656380582103081418583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81744875174109470775224777 61308656380582103081418583)
      ·
        refine ⟨91962984570873154622127875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61308656380582103081418583 91962984570873154622127875)
        ·
          refine ⟨137944476856309731933191813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91962984570873154622127875 137944476856309731933191813)
          ·
            refine ⟨25864589410558074737473465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137944476856309731933191813 25864589410558074737473465)
            ·
              refine ⟨19398442057918556053105099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25864589410558074737473465 19398442057918556053105099)
              ·
                refine ⟨29097663086877834079657649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19398442057918556053105099 29097663086877834079657649)
                ·
                  refine ⟨21823247315158375559743237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29097663086877834079657649 21823247315158375559743237)
                  ·
                    refine ⟨4091858871592195417451857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21823247315158375559743237 4091858871592195417451857)
                    ·
                      refine ⟨3068894153694146563088893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4091858871592195417451857 3068894153694146563088893)
                      ·
                        rfl

theorem cell23_5976650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_5976650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976650 prefixEnd_5976650 := by exact prefixLift 5976650
  have htrace : WordTrace (prefixWord ++ tailWord_5976650) baseStart_5976650 baseEnd_5976650 := by
    simpa [prefixWord, tailWord_5976650, baseEnd_5976650] using wordTrace_append hprefix tailTrace_5976650
  have hstable : (prefixWord ++ tailWord_5976650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976650).length < 2 ^ (prefixWord ++ tailWord_5976650).sum := by decide
  have hdescent : baseEnd_5976650 < baseStart_5976650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976660 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_5976660 : Nat := 118140960795 + 5976660 * 2 ^ 59
def prefixEnd_5976660 : Nat := 4983230072969 + 3 ^ 40 * 5976660 * 2
def baseEnd_5976660 : Nat := 1022966429500230507987949

theorem tailTrace_5976660 : CollatzResearch.WordTrace tailWord_5976660 prefixEnd_5976660 1022966429500230507987949 := by
  unfold tailWord_5976660
  simp only [CollatzResearch.WordTrace]
  refine ⟨108993349263794513554231717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145324465685059351405642289 108993349263794513554231717)
  ·
    refine ⟨20436252986961471291418447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108993349263794513554231717 20436252986961471291418447)
    ·
      refine ⟨30654379480442206937127671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20436252986961471291418447 30654379480442206937127671)
      ·
        refine ⟨45981569220663310405691507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30654379480442206937127671 45981569220663310405691507)
        ·
          refine ⟨68972353830994965608537261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45981569220663310405691507 68972353830994965608537261)
          ·
            refine ⟨25864632686623112103201473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68972353830994965608537261 25864632686623112103201473)
            ·
              refine ⟨19398474514967334077401105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25864632686623112103201473 19398474514967334077401105)
              ·
                refine ⟨14548855886225500558050829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19398474514967334077401105 14548855886225500558050829)
                ·
                  refine ⟨5455820957334562709269061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14548855886225500558050829 5455820957334562709269061)
                  ·
                    refine ⟨1022966429500230507987949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5455820957334562709269061 1022966429500230507987949)
                    ·
                      rfl

theorem cell23_5976660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_5976660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976660 prefixEnd_5976660 := by exact prefixLift 5976660
  have htrace : WordTrace (prefixWord ++ tailWord_5976660) baseStart_5976660 baseEnd_5976660 := by
    simpa [prefixWord, tailWord_5976660, baseEnd_5976660] using wordTrace_append hprefix tailTrace_5976660
  have hstable : (prefixWord ++ tailWord_5976660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976660).length < 2 ^ (prefixWord ++ tailWord_5976660).sum := by decide
  have hdescent : baseEnd_5976660 < baseStart_5976660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976666 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9]
def baseStart_5976666 : Nat := 118140960795 + 5976666 * 2 ^ 59
def prefixEnd_5976666 : Nat := 4983230072969 + 3 ^ 40 * 5976666 * 2
def baseEnd_5976666 : Nat := 3068902369384618500488819

theorem tailTrace_5976666 : CollatzResearch.WordTrace tailWord_5976666 prefixEnd_5976666 3068902369384618500488819 := by
  unfold tailWord_5976666
  simp only [CollatzResearch.WordTrace]
  refine ⟨54496729341391822533295463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145324611577044860088787901 54496729341391822533295463)
  ·
    refine ⟨81745094012087733799943195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54496729341391822533295463 81745094012087733799943195)
    ·
      refine ⟨122617641018131600699914793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81745094012087733799943195 122617641018131600699914793)
      ·
        refine ⟨91963230763598700524936095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122617641018131600699914793 91963230763598700524936095)
        ·
          refine ⟨137944846145398050787404143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91963230763598700524936095 137944846145398050787404143)
          ·
            refine ⟨206917269218097076181106215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137944846145398050787404143 206917269218097076181106215)
            ·
              refine ⟨310375903827145614271659323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206917269218097076181106215 310375903827145614271659323)
              ·
                refine ⟨465563855740718421407488985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310375903827145614271659323 465563855740718421407488985)
                ·
                  refine ⟨349172891805538816055616739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465563855740718421407488985 349172891805538816055616739)
                  ·
                    refine ⟨523759337708308224083425109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 349172891805538816055616739 523759337708308224083425109)
                    ·
                      refine ⟨3068902369384618500488819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 523759337708308224083425109 3068902369384618500488819)
                      ·
                        rfl

theorem cell23_5976666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_5976666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976666 prefixEnd_5976666 := by exact prefixLift 5976666
  have htrace : WordTrace (prefixWord ++ tailWord_5976666) baseStart_5976666 baseEnd_5976666 := by
    simpa [prefixWord, tailWord_5976666, baseEnd_5976666] using wordTrace_append hprefix tailTrace_5976666
  have hstable : (prefixWord ++ tailWord_5976666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976666).length < 2 ^ (prefixWord ++ tailWord_5976666).sum := by decide
  have hdescent : baseEnd_5976666 < baseStart_5976666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976694 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_5976694 : Nat := 118140960795 + 5976694 * 2 ^ 59
def prefixEnd_5976694 : Nat := 4983230072969 + 3 ^ 40 * 5976694 * 2
def baseEnd_5976694 : Nat := 1022972248947648130312897

theorem tailTrace_5976694 : CollatzResearch.WordTrace tailWord_5976694 prefixEnd_5976694 1022972248947648130312897 := by
  unfold tailWord_5976694
  simp only [CollatzResearch.WordTrace]
  refine ⟨13624246163091615682200071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145325292406310567276800757 13624246163091615682200071)
  ·
    refine ⟨20436369244637423523300107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13624246163091615682200071 20436369244637423523300107)
    ·
      refine ⟨30654553866956135284950161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20436369244637423523300107 30654553866956135284950161)
      ·
        refine ⟨22990915400217101463712621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30654553866956135284950161 22990915400217101463712621)
        ·
          refine ⟨8621593275081413048892233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22990915400217101463712621 8621593275081413048892233)
          ·
            refine ⟨6466194956311059786669175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8621593275081413048892233 6466194956311059786669175)
            ·
              refine ⟨9699292434466589680003763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6466194956311059786669175 9699292434466589680003763)
              ·
                refine ⟨14548938651699884520005645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9699292434466589680003763 14548938651699884520005645)
                ·
                  refine ⟨5455851994387456695002117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14548938651699884520005645 5455851994387456695002117)
                  ·
                    refine ⟨1022972248947648130312897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5455851994387456695002117 1022972248947648130312897)
                    ·
                      rfl

theorem cell23_5976694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_5976694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976694 prefixEnd_5976694 := by exact prefixLift 5976694
  have htrace : WordTrace (prefixWord ++ tailWord_5976694) baseStart_5976694 baseEnd_5976694 := by
    simpa [prefixWord, tailWord_5976694, baseEnd_5976694] using wordTrace_append hprefix tailTrace_5976694
  have hstable : (prefixWord ++ tailWord_5976694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976694).length < 2 ^ (prefixWord ++ tailWord_5976694).sum := by decide
  have hdescent : baseEnd_5976694 < baseStart_5976694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976723 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 4]
def baseStart_5976723 : Nat := 118140960795 + 5976723 * 2 ^ 59
def prefixEnd_5976723 : Nat := 4983230072969 + 3 ^ 40 * 5976723 * 2
def baseEnd_5976723 : Nat := 3068931637781924777476057

theorem tailTrace_5976723 : CollatzResearch.WordTrace tailWord_5976723 prefixEnd_5976723 3068931637781924777476057 := by
  unfold tailWord_5976723
  simp only [CollatzResearch.WordTrace]
  refine ⟨217988996326360788868006823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145325997550907192578671215 217988996326360788868006823)
  ·
    refine ⟨326983494489541183302010235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217988996326360788868006823 326983494489541183302010235)
    ·
      refine ⟨490475241734311774953015353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326983494489541183302010235 490475241734311774953015353)
      ·
        refine ⟨367856431300733831214761515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490475241734311774953015353 367856431300733831214761515)
        ·
          refine ⟨551784646951100746822142273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367856431300733831214761515 551784646951100746822142273)
          ·
            refine ⟨413838485213325560116606705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551784646951100746822142273 413838485213325560116606705)
            ·
              refine ⟨310378863909994170087455029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413838485213325560116606705 310378863909994170087455029)
              ·
                refine ⟨29098018491561953445698909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 310378863909994170087455029 29098018491561953445698909)
                ·
                  refine ⟨10911756934335732542137091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29098018491561953445698909 10911756934335732542137091)
                  ·
                    refine ⟨16367635401503598813205637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10911756934335732542137091 16367635401503598813205637)
                    ·
                      refine ⟨3068931637781924777476057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16367635401503598813205637 3068931637781924777476057)
                      ·
                        rfl

theorem cell23_5976723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 4].length) (baseStart_5976723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976723 prefixEnd_5976723 := by exact prefixLift 5976723
  have htrace : WordTrace (prefixWord ++ tailWord_5976723) baseStart_5976723 baseEnd_5976723 := by
    simpa [prefixWord, tailWord_5976723, baseEnd_5976723] using wordTrace_append hprefix tailTrace_5976723
  have hstable : (prefixWord ++ tailWord_5976723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976723).length < 2 ^ (prefixWord ++ tailWord_5976723).sum := by decide
  have hdescent : baseEnd_5976723 < baseStart_5976723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976727 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 2, 3, 2]
def baseStart_5976727 : Nat := 118140960795 + 5976727 * 2 ^ 59
def prefixEnd_5976727 : Nat := 4983230072969 + 3 ^ 40 * 5976727 * 2
def baseEnd_5976727 : Nat := 3068933691704542761826039

theorem tailTrace_5976727 : CollatzResearch.WordTrace tailWord_5976727 prefixEnd_5976727 3068933691704542761826039 := by
  unfold tailWord_5976727
  simp only [CollatzResearch.WordTrace]
  refine ⟨217989142218346297551152435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145326094812230865034101623 217989142218346297551152435)
  ·
    refine ⟨326983713327519446326728653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217989142218346297551152435 326983713327519446326728653)
    ·
      refine ⟨122618892497819792372523245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326983713327519446326728653 122618892497819792372523245)
      ·
        refine ⟨45982084686682422139696217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122618892497819792372523245 45982084686682422139696217)
        ·
          refine ⟨34486563515011816604772163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45982084686682422139696217 34486563515011816604772163)
          ·
            refine ⟨51729845272517724907158245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34486563515011816604772163 51729845272517724907158245)
            ·
              refine ⟨9699345988597073420092171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51729845272517724907158245 9699345988597073420092171)
              ·
                refine ⟨14549018982895610130138257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9699345988597073420092171 14549018982895610130138257)
                ·
                  refine ⟨10911764237171707597603693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14549018982895610130138257 10911764237171707597603693)
                  ·
                    refine ⟨4091911588939390349101385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10911764237171707597603693 4091911588939390349101385)
                    ·
                      refine ⟨3068933691704542761826039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4091911588939390349101385 3068933691704542761826039)
                      ·
                        rfl

theorem cell23_5976727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_5976727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976727 prefixEnd_5976727 := by exact prefixLift 5976727
  have htrace : WordTrace (prefixWord ++ tailWord_5976727) baseStart_5976727 baseEnd_5976727 := by
    simpa [prefixWord, tailWord_5976727, baseEnd_5976727] using wordTrace_append hprefix tailTrace_5976727
  have hstable : (prefixWord ++ tailWord_5976727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976727).length < 2 ^ (prefixWord ++ tailWord_5976727).sum := by decide
  have hdescent : baseEnd_5976727 < baseStart_5976727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976733 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 3, 6]
def baseStart_5976733 : Nat := 118140960795 + 5976733 * 2 ^ 59
def prefixEnd_5976733 : Nat := 4983230072969 + 3 ^ 40 * 5976733 * 2
def baseEnd_5976733 : Nat := 1022978924196156579450337

theorem tailTrace_5976733 : CollatzResearch.WordTrace tailWord_5976733 prefixEnd_5976733 1022978924196156579450337 := by
  unfold tailWord_5976733
  simp only [CollatzResearch.WordTrace]
  refine ⟨217989361056324560575870853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145326240704216373717247235 217989361056324560575870853)
  ·
    refine ⟨40873005198060855107975785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217989361056324560575870853 40873005198060855107975785)
    ·
      refine ⟨30654753898545641330981839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40873005198060855107975785 30654753898545641330981839)
      ·
        refine ⟨45982130847818461996472759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30654753898545641330981839 45982130847818461996472759)
        ·
          refine ⟨68973196271727692994709139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45982130847818461996472759 68973196271727692994709139)
          ·
            refine ⟨103459794407591539492063709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68973196271727692994709139 103459794407591539492063709)
            ·
              refine ⟨38797422902846827309523891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103459794407591539492063709 38797422902846827309523891)
              ·
                refine ⟨58196134354270240964285837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38797422902846827309523891 58196134354270240964285837)
                ·
                  refine ⟨21823550382851340361607189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58196134354270240964285837 21823550382851340361607189)
                  ·
                    refine ⟨1022978924196156579450337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21823550382851340361607189 1022978924196156579450337)
                    ·
                      rfl

theorem cell23_5976733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_5976733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976733 prefixEnd_5976733 := by exact prefixLift 5976733
  have htrace : WordTrace (prefixWord ++ tailWord_5976733) baseStart_5976733 baseEnd_5976733 := by
    simpa [prefixWord, tailWord_5976733, baseEnd_5976733] using wordTrace_append hprefix tailTrace_5976733
  have hstable : (prefixWord ++ tailWord_5976733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976733).length < 2 ^ (prefixWord ++ tailWord_5976733).sum := by decide
  have hdescent : baseEnd_5976733 < baseStart_5976733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976751 : List Nat := [1, 1, 2, 1, 2, 7, 2, 2, 1, 1, 3]
def baseStart_5976751 : Nat := 118140960795 + 5976751 * 2 ^ 59
def prefixEnd_5976751 : Nat := 4983230072969 + 3 ^ 40 * 5976751 * 2
def baseEnd_5976751 : Nat := 3068946015240250667925929

theorem tailTrace_5976751 : CollatzResearch.WordTrace tailWord_5976751 prefixEnd_5976751 3068946015240250667925929 := by
  unfold tailWord_5976751
  simp only [CollatzResearch.WordTrace]
  refine ⟨217990017570259349650026107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145326678380172899766684071 217990017570259349650026107)
  ·
    refine ⟨326985026355389024475039161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217990017570259349650026107 326985026355389024475039161)
    ·
      refine ⟨245238769766541768356279371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326985026355389024475039161 245238769766541768356279371)
      ·
        refine ⟨367858154649812652534419057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245238769766541768356279371 367858154649812652534419057)
        ·
          refine ⟨275893615987359489400814293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367858154649812652534419057 275893615987359489400814293)
          ·
            refine ⟨6466256624703738032831585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 275893615987359489400814293 6466256624703738032831585)
            ·
              refine ⟨4849692468527803524623689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6466256624703738032831585 4849692468527803524623689)
              ·
                refine ⟨3637269351395852643467767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4849692468527803524623689 3637269351395852643467767)
                ·
                  refine ⟨5455904027093778965201651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3637269351395852643467767 5455904027093778965201651)
                  ·
                    refine ⟨8183856040640668447802477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5455904027093778965201651 8183856040640668447802477)
                    ·
                      refine ⟨3068946015240250667925929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8183856040640668447802477 3068946015240250667925929)
                      ·
                        rfl

theorem cell23_5976751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 1, 1, 3].length) (baseStart_5976751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976751 prefixEnd_5976751 := by exact prefixLift 5976751
  have htrace : WordTrace (prefixWord ++ tailWord_5976751) baseStart_5976751 baseEnd_5976751 := by
    simpa [prefixWord, tailWord_5976751, baseEnd_5976751] using wordTrace_append hprefix tailTrace_5976751
  have hstable : (prefixWord ++ tailWord_5976751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976751).length < 2 ^ (prefixWord ++ tailWord_5976751).sum := by decide
  have hdescent : baseEnd_5976751 < baseStart_5976751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976791 : List Nat := [1, 1, 3, 2, 1, 5, 2, 3, 1, 2, 2]
def baseStart_5976791 : Nat := 118140960795 + 5976791 * 2 ^ 59
def prefixEnd_5976791 : Nat := 4983230072969 + 3 ^ 40 * 5976791 * 2
def baseEnd_5976791 : Nat := 3068966554466430511425745

theorem tailTrace_5976791 : CollatzResearch.WordTrace tailWord_5976791 prefixEnd_5976791 3068966554466430511425745 := by
  unfold tailWord_5976791
  simp only [CollatzResearch.WordTrace]
  refine ⟨217991476490114436481482227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145327650993409624320988151 217991476490114436481482227)
  ·
    refine ⟨326987214735171654722223341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217991476490114436481482227 326987214735171654722223341)
    ·
      refine ⟨122620205525689370520833753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326987214735171654722223341 122620205525689370520833753)
      ·
        refine ⟨91965154144267027890625315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122620205525689370520833753 91965154144267027890625315)
        ·
          refine ⟨137947731216400541835937973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91965154144267027890625315 137947731216400541835937973)
          ·
            refine ⟨12932599801537550797119185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137947731216400541835937973 12932599801537550797119185)
            ·
              refine ⟨9699449851153163097839389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12932599801537550797119185 9699449851153163097839389)
              ·
                refine ⟨3637293694182436161689771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9699449851153163097839389 3637293694182436161689771)
                ·
                  refine ⟨5455940541273654242534657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3637293694182436161689771 5455940541273654242534657)
                  ·
                    refine ⟨4091955405955240681900993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5455940541273654242534657 4091955405955240681900993)
                    ·
                      refine ⟨3068966554466430511425745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4091955405955240681900993 3068966554466430511425745)
                      ·
                        rfl

theorem cell23_5976791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_5976791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976791 prefixEnd_5976791 := by exact prefixLift 5976791
  have htrace : WordTrace (prefixWord ++ tailWord_5976791) baseStart_5976791 baseEnd_5976791 := by
    simpa [prefixWord, tailWord_5976791, baseEnd_5976791] using wordTrace_append hprefix tailTrace_5976791
  have hstable : (prefixWord ++ tailWord_5976791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976791).length < 2 ^ (prefixWord ++ tailWord_5976791).sum := by decide
  have hdescent : baseEnd_5976791 < baseStart_5976791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976824 : List Nat := [2, 1, 2, 1, 1, 2, 7, 1, 2, 1, 3]
def baseStart_5976824 : Nat := 118140960795 + 5976824 * 2 ^ 59
def prefixEnd_5976824 : Nat := 4983230072969 + 3 ^ 40 * 5976824 * 2
def baseEnd_5976824 : Nat := 3068983499328028882313093

theorem tailTrace_5976824 : CollatzResearch.WordTrace tailWord_5976824 prefixEnd_5976824 3068983499328028882313093 := by
  unfold tailWord_5976824
  simp only [CollatzResearch.WordTrace]
  refine ⟨108996340049497441558716763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145328453399329922078289017 108996340049497441558716763)
  ·
    refine ⟨163494510074246162338075145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108996340049497441558716763 163494510074246162338075145)
    ·
      refine ⟨122620882555684621753556359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163494510074246162338075145 122620882555684621753556359)
      ·
        refine ⟨183931323833526932630334539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122620882555684621753556359 183931323833526932630334539)
        ·
          refine ⟨275896985750290398945501809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183931323833526932630334539 275896985750290398945501809)
          ·
            refine ⟨206922739312717799209126357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275896985750290398945501809 206922739312717799209126357)
            ·
              refine ⟨4849751702641823418963899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 206922739312717799209126357 4849751702641823418963899)
              ·
                refine ⟨7274627553962735128445849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4849751702641823418963899 7274627553962735128445849)
                ·
                  refine ⟨5455970665472051346334387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7274627553962735128445849 5455970665472051346334387)
                  ·
                    refine ⟨8183955998208077019501581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5455970665472051346334387 8183955998208077019501581)
                    ·
                      refine ⟨3068983499328028882313093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8183955998208077019501581 3068983499328028882313093)
                      ·
                        rfl

theorem cell23_5976824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 2, 1, 3].length) (baseStart_5976824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976824 prefixEnd_5976824 := by exact prefixLift 5976824
  have htrace : WordTrace (prefixWord ++ tailWord_5976824) baseStart_5976824 baseEnd_5976824 := by
    simpa [prefixWord, tailWord_5976824, baseEnd_5976824] using wordTrace_append hprefix tailTrace_5976824
  have hstable : (prefixWord ++ tailWord_5976824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976824).length < 2 ^ (prefixWord ++ tailWord_5976824).sum := by decide
  have hdescent : baseEnd_5976824 < baseStart_5976824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976847 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 6, 2, 2]
def baseStart_5976847 : Nat := 118140960795 + 5976847 * 2 ^ 59
def prefixEnd_5976847 : Nat := 4983230072969 + 3 ^ 40 * 5976847 * 2
def baseEnd_5976847 : Nat := 3068995309383082292325487

theorem tailTrace_5976847 : CollatzResearch.WordTrace tailWord_5976847 prefixEnd_5976847 3068995309383082292325487 := by
  unfold tailWord_5976847
  simp only [CollatzResearch.WordTrace]
  refine ⟨217993518977911558045520795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145329012651941038697013863 217993518977911558045520795)
  ·
    refine ⟨326990278466867337068281193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217993518977911558045520795 326990278466867337068281193)
    ·
      refine ⟨245242708850150502801210895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326990278466867337068281193 245242708850150502801210895)
      ·
        refine ⟨367864063275225754201816343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245242708850150502801210895 367864063275225754201816343)
        ·
          refine ⟨551796094912838631302724515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367864063275225754201816343 551796094912838631302724515)
          ·
            refine ⟨827694142369257946954086773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551796094912838631302724515 827694142369257946954086773)
            ·
              refine ⟨77596325847117932526945635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 827694142369257946954086773 77596325847117932526945635)
              ·
                refine ⟨116394488770676898790418453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77596325847117932526945635 116394488770676898790418453)
                ·
                  refine ⟨5455991661125479630800865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116394488770676898790418453 5455991661125479630800865)
                  ·
                    refine ⟨4091993745844109723100649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5455991661125479630800865 4091993745844109723100649)
                    ·
                      refine ⟨3068995309383082292325487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4091993745844109723100649 3068995309383082292325487)
                      ·
                        rfl

theorem cell23_5976847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 2, 2].length) (baseStart_5976847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976847 prefixEnd_5976847 := by exact prefixLift 5976847
  have htrace : WordTrace (prefixWord ++ tailWord_5976847) baseStart_5976847 baseEnd_5976847 := by
    simpa [prefixWord, tailWord_5976847, baseEnd_5976847] using wordTrace_append hprefix tailTrace_5976847
  have hstable : (prefixWord ++ tailWord_5976847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976847).length < 2 ^ (prefixWord ++ tailWord_5976847).sum := by decide
  have hdescent : baseEnd_5976847 < baseStart_5976847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976864 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 4, 2, 2]
def baseStart_5976864 : Nat := 118140960795 + 5976864 * 2 ^ 59
def prefixEnd_5976864 : Nat := 4983230072969 + 3 ^ 40 * 5976864 * 2
def baseEnd_5976864 : Nat := 3069004038554208725812909

theorem tailTrace_5976864 : CollatzResearch.WordTrace tailWord_5976864 prefixEnd_5976864 3069004038554208725812909 := by
  unfold tailWord_5976864
  simp only [CollatzResearch.WordTrace]
  refine ⟨108997069509424984974444823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145329426012566646632593097 108997069509424984974444823)
  ·
    refine ⟨163495604264137477461667235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108997069509424984974444823 163495604264137477461667235)
    ·
      refine ⟨245243406396206216192500853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163495604264137477461667235 245243406396206216192500853)
      ·
        refine ⟨22991569349644332768046955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 245243406396206216192500853 22991569349644332768046955)
        ·
          refine ⟨34487354024466499152070433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22991569349644332768046955 34487354024466499152070433)
          ·
            refine ⟨25865515518349874364052825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34487354024466499152070433 25865515518349874364052825)
            ·
              refine ⟨19399136638762405773039619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25865515518349874364052825 19399136638762405773039619)
              ·
                refine ⟨29098704958143608659559429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19399136638762405773039619 29098704958143608659559429)
                ·
                  refine ⟨5456007179651926623667393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29098704958143608659559429 5456007179651926623667393)
                  ·
                    refine ⟨4092005384738944967750545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5456007179651926623667393 4092005384738944967750545)
                    ·
                      refine ⟨3069004038554208725812909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4092005384738944967750545 3069004038554208725812909)
                      ·
                        rfl

theorem cell23_5976864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_5976864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976864 prefixEnd_5976864 := by exact prefixLift 5976864
  have htrace : WordTrace (prefixWord ++ tailWord_5976864) baseStart_5976864 baseEnd_5976864 := by
    simpa [prefixWord, tailWord_5976864, baseEnd_5976864] using wordTrace_append hprefix tailTrace_5976864
  have hstable : (prefixWord ++ tailWord_5976864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976864).length < 2 ^ (prefixWord ++ tailWord_5976864).sum := by decide
  have hdescent : baseEnd_5976864 < baseStart_5976864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976880 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 3]
def baseStart_5976880 : Nat := 118140960795 + 5976880 * 2 ^ 59
def prefixEnd_5976880 : Nat := 4983230072969 + 3 ^ 40 * 5976880 * 2
def baseEnd_5976880 : Nat := 3069012254244680663212835

theorem tailTrace_5976880 : CollatzResearch.WordTrace tailWord_5976880 prefixEnd_5976880 3069012254244680663212835 := by
  unfold tailWord_5976880
  simp only [CollatzResearch.WordTrace]
  refine ⟨108997361293396002340736047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145329815057861336454314729 108997361293396002340736047)
  ·
    refine ⟨163496041940094003511104071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108997361293396002340736047 163496041940094003511104071)
    ·
      refine ⟨245244062910141005266656107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163496041940094003511104071 245244062910141005266656107)
      ·
        refine ⟨367866094365211507899984161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245244062910141005266656107 367866094365211507899984161)
        ·
          refine ⟨275899570773908630924988121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367866094365211507899984161 275899570773908630924988121)
          ·
            refine ⟨206924678080431473193741091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275899570773908630924988121 206924678080431473193741091)
            ·
              refine ⟨310387017120647209790611637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206924678080431473193741091 310387017120647209790611637)
              ·
                refine ⟨29098782855060675917869841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 310387017120647209790611637 29098782855060675917869841)
                ·
                  refine ⟨21824087141295506938402381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29098782855060675917869841 21824087141295506938402381)
                  ·
                    refine ⟨8184032677985815101900893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21824087141295506938402381 8184032677985815101900893)
                    ·
                      refine ⟨3069012254244680663212835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8184032677985815101900893 3069012254244680663212835)
                      ·
                        rfl

theorem cell23_5976880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 3].length) (baseStart_5976880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976880 prefixEnd_5976880 := by exact prefixLift 5976880
  have htrace : WordTrace (prefixWord ++ tailWord_5976880) baseStart_5976880 baseEnd_5976880 := by
    simpa [prefixWord, tailWord_5976880, baseEnd_5976880] using wordTrace_append hprefix tailTrace_5976880
  have hstable : (prefixWord ++ tailWord_5976880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976880).length < 2 ^ (prefixWord ++ tailWord_5976880).sum := by decide
  have hdescent : baseEnd_5976880 < baseStart_5976880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5976924 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_5976924 : Nat := 118140960795 + 5976924 * 2 ^ 59
def prefixEnd_5976924 : Nat := 4983230072969 + 3 ^ 40 * 5976924 * 2
def baseEnd_5976924 : Nat := 3069034847393478491062633

theorem tailTrace_5976924 : CollatzResearch.WordTrace tailWord_5976924 prefixEnd_5976924 3069034847393478491062633 := by
  unfold tailWord_5976924
  simp only [CollatzResearch.WordTrace]
  refine ⟨108998163699316300098036913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145330884932421733464049217 108998163699316300098036913)
  ·
    refine ⟨81748622774487225073527685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108998163699316300098036913 81748622774487225073527685)
    ·
      refine ⟨15327866770216354701286441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81748622774487225073527685 15327866770216354701286441)
      ·
        refine ⟨11495900077662266025964831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15327866770216354701286441 11495900077662266025964831)
        ·
          refine ⟨17243850116493399038947247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11495900077662266025964831 17243850116493399038947247)
          ·
            refine ⟨25865775174740098558420871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17243850116493399038947247 25865775174740098558420871)
            ·
              refine ⟨38798662762110147837631307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25865775174740098558420871 38798662762110147837631307)
              ·
                refine ⟨58197994143165221756446961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38798662762110147837631307 58197994143165221756446961)
                ·
                  refine ⟨43648495607373916317335221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58197994143165221756446961 43648495607373916317335221)
                  ·
                    refine ⟨4092046463191304654750177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43648495607373916317335221 4092046463191304654750177)
                    ·
                      refine ⟨3069034847393478491062633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4092046463191304654750177 3069034847393478491062633)
                      ·
                        rfl

theorem cell23_5976924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_5976924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5976924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5976924 prefixEnd_5976924 := by exact prefixLift 5976924
  have htrace : WordTrace (prefixWord ++ tailWord_5976924) baseStart_5976924 baseEnd_5976924 := by
    simpa [prefixWord, tailWord_5976924, baseEnd_5976924] using wordTrace_append hprefix tailTrace_5976924
  have hstable : (prefixWord ++ tailWord_5976924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5976924).length < 2 ^ (prefixWord ++ tailWord_5976924).sum := by decide
  have hdescent : baseEnd_5976924 < baseStart_5976924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5976924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977027 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 1, 8, 2]
def baseStart_5977027 : Nat := 118140960795 + 5977027 * 2 ^ 59
def prefixEnd_5977027 : Nat := 4983230072969 + 3 ^ 40 * 5977027 * 2
def baseEnd_5977027 : Nat := 3069087735900891588074659

theorem tailTrace_5977027 : CollatzResearch.WordTrace tailWord_5977027 prefixEnd_5977027 3069087735900891588074659 := by
  unfold tailWord_5977027
  simp only [CollatzResearch.WordTrace]
  refine ⟨218000084117259448787073335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145333389411506299191382223 218000084117259448787073335)
  ·
    refine ⟨327000126175889173180610003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218000084117259448787073335 327000126175889173180610003)
    ·
      refine ⟨490500189263833759770915005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327000126175889173180610003 490500189263833759770915005)
      ·
        refine ⟨183937570973937659914093127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 490500189263833759770915005 183937570973937659914093127)
        ·
          refine ⟨275906356460906489871139691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183937570973937659914093127 275906356460906489871139691)
          ·
            refine ⟨413859534691359734806709537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275906356460906489871139691 413859534691359734806709537)
            ·
              refine ⟨310394651018519801105032153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413859534691359734806709537 310394651018519801105032153)
              ·
                refine ⟨232795988263889850828774115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310394651018519801105032153 232795988263889850828774115)
                ·
                  refine ⟨349193982395834776243161173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232795988263889850828774115 349193982395834776243161173)
                  ·
                    refine ⟨4092116981201188784099545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 349193982395834776243161173 4092116981201188784099545)
                    ·
                      refine ⟨3069087735900891588074659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4092116981201188784099545 3069087735900891588074659)
                      ·
                        rfl

theorem cell23_5977027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 8, 2].length) (baseStart_5977027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977027 prefixEnd_5977027 := by exact prefixLift 5977027
  have htrace : WordTrace (prefixWord ++ tailWord_5977027) baseStart_5977027 baseEnd_5977027 := by
    simpa [prefixWord, tailWord_5977027, baseEnd_5977027] using wordTrace_append hprefix tailTrace_5977027
  have hstable : (prefixWord ++ tailWord_5977027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977027).length < 2 ^ (prefixWord ++ tailWord_5977027).sum := by decide
  have hdescent : baseEnd_5977027 < baseStart_5977027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977057 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_5977057 : Nat := 118140960795 + 5977057 * 2 ^ 59
def prefixEnd_5977057 : Nat := 4983230072969 + 3 ^ 40 * 5977057 * 2
def baseEnd_5977057 : Nat := 3069103140320526470699521

theorem tailTrace_5977057 : CollatzResearch.WordTrace tailWord_5977057 prefixEnd_5977057 3069103140320526470699521 := by
  unfold tailWord_5977057
  simp only [CollatzResearch.WordTrace]
  refine ⟨218001178307150763910665425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145334118871433842607110283 218001178307150763910665425)
  ·
    refine ⟨163500883730363072932999069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218001178307150763910665425 163500883730363072932999069)
    ·
      refine ⟨61312831398886152349874651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163500883730363072932999069 61312831398886152349874651)
      ·
        refine ⟨91969247098329228524811977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61312831398886152349874651 91969247098329228524811977)
        ·
          refine ⟨68976935323746921393608983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91969247098329228524811977 68976935323746921393608983)
          ·
            refine ⟨103465402985620382090413475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68976935323746921393608983 103465402985620382090413475)
            ·
              refine ⟨155198104478430573135620213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103465402985620382090413475 155198104478430573135620213)
              ·
                refine ⟨14549822294852866231464395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 155198104478430573135620213 14549822294852866231464395)
                ·
                  refine ⟨21824733442279299347196593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14549822294852866231464395 21824733442279299347196593)
                  ·
                    refine ⟨16368550081709474510397445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21824733442279299347196593 16368550081709474510397445)
                    ·
                      refine ⟨3069103140320526470699521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16368550081709474510397445 3069103140320526470699521)
                      ·
                        rfl

theorem cell23_5977057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_5977057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977057 prefixEnd_5977057 := by exact prefixLift 5977057
  have htrace : WordTrace (prefixWord ++ tailWord_5977057) baseStart_5977057 baseEnd_5977057 := by
    simpa [prefixWord, tailWord_5977057, baseEnd_5977057] using wordTrace_append hprefix tailTrace_5977057
  have hstable : (prefixWord ++ tailWord_5977057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977057).length < 2 ^ (prefixWord ++ tailWord_5977057).sum := by decide
  have hdescent : baseEnd_5977057 < baseStart_5977057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977058 : List Nat := [3, 3, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_5977058 : Nat := 118140960795 + 5977058 * 2 ^ 59
def prefixEnd_5977058 : Nat := 4983230072969 + 3 ^ 40 * 5977058 * 2
def baseEnd_5977058 : Nat := 1023034551267060322262339

theorem tailTrace_5977058 : CollatzResearch.WordTrace tailWord_5977058 prefixEnd_5977058 1023034551267060322262339 := by
  unfold tailWord_5977058
  simp only [CollatzResearch.WordTrace]
  refine ⟨54500303695036785270362957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145334143186764760720967885 54500303695036785270362957)
  ·
    refine ⟨20437613885638794476386109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54500303695036785270362957 20437613885638794476386109)
    ·
      refine ⟨7664105207114547928644791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20437613885638794476386109 7664105207114547928644791)
      ·
        refine ⟨11496157810671821892967187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7664105207114547928644791 11496157810671821892967187)
        ·
          refine ⟨17244236716007732839450781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11496157810671821892967187 17244236716007732839450781)
          ·
            refine ⟨6466588768502899814794043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17244236716007732839450781 6466588768502899814794043)
            ·
              refine ⟨9699883152754349722191065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6466588768502899814794043 9699883152754349722191065)
              ·
                refine ⟨7274912364565762291643299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9699883152754349722191065 7274912364565762291643299)
                ·
                  refine ⟨10912368546848643437464949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7274912364565762291643299 10912368546848643437464949)
                  ·
                    refine ⟨1023034551267060322262339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10912368546848643437464949 1023034551267060322262339)
                    ·
                      rfl

theorem cell23_5977058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_5977058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977058 prefixEnd_5977058 := by exact prefixLift 5977058
  have htrace : WordTrace (prefixWord ++ tailWord_5977058) baseStart_5977058 baseEnd_5977058 := by
    simpa [prefixWord, tailWord_5977058, baseEnd_5977058] using wordTrace_append hprefix tailTrace_5977058
  have hstable : (prefixWord ++ tailWord_5977058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977058).length < 2 ^ (prefixWord ++ tailWord_5977058).sum := by decide
  have hdescent : baseEnd_5977058 < baseStart_5977058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977061 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 3, 1, 4]
def baseStart_5977061 : Nat := 118140960795 + 5977061 * 2 ^ 59
def prefixEnd_5977061 : Nat := 4983230072969 + 3 ^ 40 * 5977061 * 2
def baseEnd_5977061 : Nat := 3069105194243144455049503

theorem tailTrace_5977061 : CollatzResearch.WordTrace tailWord_5977061 prefixEnd_5977061 3069105194243144455049503 := by
  unfold tailWord_5977061
  simp only [CollatzResearch.WordTrace]
  refine ⟨218001324199136272593811037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145334216132757515062540691 218001324199136272593811037)
  ·
    refine ⟨81750496574676102222679139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218001324199136272593811037 81750496574676102222679139)
    ·
      refine ⟨122625744862014153334018709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81750496574676102222679139 122625744862014153334018709)
      ·
        refine ⟨5748081790406913437532127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122625744862014153334018709 5748081790406913437532127)
        ·
          refine ⟨8622122685610370156298191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5748081790406913437532127 8622122685610370156298191)
          ·
            refine ⟨12933184028415555234447287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8622122685610370156298191 12933184028415555234447287)
            ·
              refine ⟨19399776042623332851670931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12933184028415555234447287 19399776042623332851670931)
              ·
                refine ⟨29099664063934999277506397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19399776042623332851670931 29099664063934999277506397)
                ·
                  refine ⟨10912374023975624729064899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29099664063934999277506397 10912374023975624729064899)
                  ·
                    refine ⟨16368561035963437093597349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10912374023975624729064899 16368561035963437093597349)
                    ·
                      refine ⟨3069105194243144455049503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16368561035963437093597349 3069105194243144455049503)
                      ·
                        rfl

theorem cell23_5977061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_5977061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977061 prefixEnd_5977061 := by exact prefixLift 5977061
  have htrace : WordTrace (prefixWord ++ tailWord_5977061) baseStart_5977061 baseEnd_5977061 := by
    simpa [prefixWord, tailWord_5977061, baseEnd_5977061] using wordTrace_append hprefix tailTrace_5977061
  have hstable : (prefixWord ++ tailWord_5977061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977061).length < 2 ^ (prefixWord ++ tailWord_5977061).sum := by decide
  have hdescent : baseEnd_5977061 < baseStart_5977061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977078 : List Nat := [5, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4]
def baseStart_5977078 : Nat := 118140960795 + 5977078 * 2 ^ 59
def prefixEnd_5977078 : Nat := 4983230072969 + 3 ^ 40 * 5977078 * 2
def baseEnd_5977078 : Nat := 3069113923414270888536925

theorem tailTrace_5977078 : CollatzResearch.WordTrace tailWord_5977078 prefixEnd_5977078 3069113923414270888536925 := by
  unfold tailWord_5977078
  simp only [CollatzResearch.WordTrace]
  refine ⟨13625121515004667781073743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145334629493383122998119925 13625121515004667781073743)
  ·
    refine ⟨20437682272507001671610615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13625121515004667781073743 20437682272507001671610615)
    ·
      refine ⟨30656523408760502507415923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20437682272507001671610615 30656523408760502507415923)
      ·
        refine ⟨45984785113140753761123885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30656523408760502507415923 45984785113140753761123885)
        ·
          refine ⟨17244294417427782660421457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45984785113140753761123885 17244294417427782660421457)
          ·
            refine ⟨12933220813070836995316093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17244294417427782660421457 12933220813070836995316093)
            ·
              refine ⟨4849957804901563873243535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12933220813070836995316093 4849957804901563873243535)
              ·
                refine ⟨7274936707352345809865303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4849957804901563873243535 7274936707352345809865303)
                ·
                  refine ⟨10912405061028518714797955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7274936707352345809865303 10912405061028518714797955)
                  ·
                    refine ⟨16368607591542778072196933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10912405061028518714797955 16368607591542778072196933)
                    ·
                      refine ⟨3069113923414270888536925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16368607591542778072196933 3069113923414270888536925)
                      ·
                        rfl

theorem cell23_5977078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_5977078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977078 prefixEnd_5977078 := by exact prefixLift 5977078
  have htrace : WordTrace (prefixWord ++ tailWord_5977078) baseStart_5977078 baseEnd_5977078 := by
    simpa [prefixWord, tailWord_5977078, baseEnd_5977078] using wordTrace_append hprefix tailTrace_5977078
  have hstable : (prefixWord ++ tailWord_5977078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977078).length < 2 ^ (prefixWord ++ tailWord_5977078).sum := by decide
  have hdescent : baseEnd_5977078 < baseStart_5977078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977081 : List Nat := [1, 2, 1, 3, 1, 3, 5, 1, 1, 2, 3]
def baseStart_5977081 : Nat := 118140960795 + 5977081 * 2 ^ 59
def prefixEnd_5977081 : Nat := 4983230072969 + 3 ^ 40 * 5977081 * 2
def baseEnd_5977081 : Nat := 3069115463856234376799411

theorem tailTrace_5977081 : CollatzResearch.WordTrace tailWord_5977081 prefixEnd_5977081 3069115463856234376799411 := by
  unfold tailWord_5977081
  simp only [CollatzResearch.WordTrace]
  refine ⟨218002053659063816009539097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145334702439375877339692731 218002053659063816009539097)
  ·
    refine ⟨163501540244297862007154323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218002053659063816009539097 163501540244297862007154323)
    ·
      refine ⟨245252310366446793010731485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163501540244297862007154323 245252310366446793010731485)
      ·
        refine ⟨91969616387417547379024307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245252310366446793010731485 91969616387417547379024307)
        ·
          refine ⟨137954424581126321068536461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91969616387417547379024307 137954424581126321068536461)
          ·
            refine ⟨51732909217922370400701173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137954424581126321068536461 51732909217922370400701173)
            ·
              refine ⟨4849960239180222225065735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51732909217922370400701173 4849960239180222225065735)
              ·
                refine ⟨7274940358770333337598603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4849960239180222225065735 7274940358770333337598603)
                ·
                  refine ⟨10912410538155500006397905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7274940358770333337598603 10912410538155500006397905)
                  ·
                    refine ⟨8184307903616625004798429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10912410538155500006397905 8184307903616625004798429)
                    ·
                      refine ⟨3069115463856234376799411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8184307903616625004798429 3069115463856234376799411)
                      ·
                        rfl

theorem cell23_5977081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_5977081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977081 prefixEnd_5977081 := by exact prefixLift 5977081
  have htrace : WordTrace (prefixWord ++ tailWord_5977081) baseStart_5977081 baseEnd_5977081 := by
    simpa [prefixWord, tailWord_5977081, baseEnd_5977081] using wordTrace_append hprefix tailTrace_5977081
  have hstable : (prefixWord ++ tailWord_5977081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977081).length < 2 ^ (prefixWord ++ tailWord_5977081).sum := by decide
  have hdescent : baseEnd_5977081 < baseStart_5977081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977111 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 3]
def baseStart_5977111 : Nat := 118140960795 + 5977111 * 2 ^ 59
def prefixEnd_5977111 : Nat := 4983230072969 + 3 ^ 40 * 5977111 * 2
def baseEnd_5977111 : Nat := 3069130868275869259424273

theorem tailTrace_5977111 : CollatzResearch.WordTrace tailWord_5977111 prefixEnd_5977111 3069130868275869259424273 := by
  unfold tailWord_5977111
  simp only [CollatzResearch.WordTrace]
  refine ⟨218003147848955131133131187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145335431899303420755420791 218003147848955131133131187)
  ·
    refine ⟨327004721773432696699696781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218003147848955131133131187 327004721773432696699696781)
    ·
      refine ⟨122626770665037261262386293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327004721773432696699696781 122626770665037261262386293)
      ·
        refine ⟨11496259749847243243348715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122626770665037261262386293 11496259749847243243348715)
        ·
          refine ⟨17244389624770864865023073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11496259749847243243348715 17244389624770864865023073)
          ·
            refine ⟨12933292218578148648767305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17244389624770864865023073 12933292218578148648767305)
            ·
              refine ⟨9699969163933611486575479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12933292218578148648767305 9699969163933611486575479)
              ·
                refine ⟨14549953745900417229863219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9699969163933611486575479 14549953745900417229863219)
                ·
                  refine ⟨21824930618850625844794829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14549953745900417229863219 21824930618850625844794829)
                  ·
                    refine ⟨8184348982068984691798061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21824930618850625844794829 8184348982068984691798061)
                    ·
                      refine ⟨3069130868275869259424273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8184348982068984691798061 3069130868275869259424273)
                      ·
                        rfl

theorem cell23_5977111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_5977111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977111 prefixEnd_5977111 := by exact prefixLift 5977111
  have htrace : WordTrace (prefixWord ++ tailWord_5977111) baseStart_5977111 baseEnd_5977111 := by
    simpa [prefixWord, tailWord_5977111, baseEnd_5977111] using wordTrace_append hprefix tailTrace_5977111
  have hstable : (prefixWord ++ tailWord_5977111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977111).length < 2 ^ (prefixWord ++ tailWord_5977111).sum := by decide
  have hdescent : baseEnd_5977111 < baseStart_5977111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977121 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 3, 3, 2]
def baseStart_5977121 : Nat := 118140960795 + 5977121 * 2 ^ 59
def prefixEnd_5977121 : Nat := 4983230072969 + 3 ^ 40 * 5977121 * 2
def baseEnd_5977121 : Nat := 3069136003082414220299227

theorem tailTrace_5977121 : CollatzResearch.WordTrace tailWord_5977121 prefixEnd_5977121 3069136003082414220299227 := by
  unfold tailWord_5977121
  simp only [CollatzResearch.WordTrace]
  refine ⟨218003512578918902840995217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145335675052612601893996811 218003512578918902840995217)
  ·
    refine ⟨163502634434189177130746413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218003512578918902840995217 163502634434189177130746413)
    ·
      refine ⟨61313487912820941424029905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163502634434189177130746413 61313487912820941424029905)
      ·
        refine ⟨45985115934615706068022429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61313487912820941424029905 45985115934615706068022429)
        ·
          refine ⟨17244418475480889775508411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45985115934615706068022429 17244418475480889775508411)
          ·
            refine ⟨25866627713221334663262617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17244418475480889775508411 25866627713221334663262617)
            ·
              refine ⟨19399970784916000997446963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25866627713221334663262617 19399970784916000997446963)
              ·
                refine ⟨29099956177374001496170445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19399970784916000997446963 29099956177374001496170445)
                ·
                  refine ⟨10912483566515250561063917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29099956177374001496170445 10912483566515250561063917)
                  ·
                    refine ⟨4092181337443218960398969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10912483566515250561063917 4092181337443218960398969)
                    ·
                      refine ⟨3069136003082414220299227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4092181337443218960398969 3069136003082414220299227)
                      ·
                        rfl

theorem cell23_5977121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_5977121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977121 prefixEnd_5977121 := by exact prefixLift 5977121
  have htrace : WordTrace (prefixWord ++ tailWord_5977121) baseStart_5977121 baseEnd_5977121 := by
    simpa [prefixWord, tailWord_5977121, baseEnd_5977121] using wordTrace_append hprefix tailTrace_5977121
  have hstable : (prefixWord ++ tailWord_5977121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977121).length < 2 ^ (prefixWord ++ tailWord_5977121).sum := by decide
  have hdescent : baseEnd_5977121 < baseStart_5977121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977137 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 1, 3, 5]
def baseStart_5977137 : Nat := 118140960795 + 5977137 * 2 ^ 59
def prefixEnd_5977137 : Nat := 4983230072969 + 3 ^ 40 * 5977137 * 2
def baseEnd_5977137 : Nat := 3069144218772886157699153

theorem tailTrace_5977137 : CollatzResearch.WordTrace tailWord_5977137 prefixEnd_5977137 3069144218772886157699153 := by
  unfold tailWord_5977137
  simp only [CollatzResearch.WordTrace]
  refine ⟨218004096146860937573577665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145336064097907291715718443 218004096146860937573577665)
  ·
    refine ⟨163503072110145703180183249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218004096146860937573577665 163503072110145703180183249)
    ·
      refine ⟨122627304082609277385137437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163503072110145703180183249 122627304082609277385137437)
      ·
        refine ⟨45985239030978479019426539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122627304082609277385137437 45985239030978479019426539)
        ·
          refine ⟨68977858546467718529139809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45985239030978479019426539 68977858546467718529139809)
          ·
            refine ⟨51733393909850788896854857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68977858546467718529139809 51733393909850788896854857)
            ·
              refine ⟨38800045432388091672641143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51733393909850788896854857 38800045432388091672641143)
              ·
                refine ⟨58200068148582137508961715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38800045432388091672641143 58200068148582137508961715)
                ·
                  refine ⟨87300102222873206263442573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58200068148582137508961715 87300102222873206263442573)
                  ·
                    refine ⟨32737538333577452348790965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87300102222873206263442573 32737538333577452348790965)
                    ·
                      refine ⟨3069144218772886157699153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32737538333577452348790965 3069144218772886157699153)
                      ·
                        rfl

theorem cell23_5977137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_5977137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977137 prefixEnd_5977137 := by exact prefixLift 5977137
  have htrace : WordTrace (prefixWord ++ tailWord_5977137) baseStart_5977137 baseEnd_5977137 := by
    simpa [prefixWord, tailWord_5977137, baseEnd_5977137] using wordTrace_append hprefix tailTrace_5977137
  have hstable : (prefixWord ++ tailWord_5977137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977137).length < 2 ^ (prefixWord ++ tailWord_5977137).sum := by decide
  have hdescent : baseEnd_5977137 < baseStart_5977137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977157 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 7]
def baseStart_5977157 : Nat := 118140960795 + 5977157 * 2 ^ 59
def prefixEnd_5977157 : Nat := 4983230072969 + 3 ^ 40 * 5977157 * 2
def baseEnd_5977157 : Nat := 341017165376219564383229

theorem tailTrace_5977157 : CollatzResearch.WordTrace tailWord_5977157 prefixEnd_5977157 341017165376219564383229 := by
  unfold tailWord_5977157
  simp only [CollatzResearch.WordTrace]
  refine ⟨218004825606788480989305725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145336550404525653992870483 218004825606788480989305725)
  ·
    refine ⟨81751809602545680370989647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218004825606788480989305725 81751809602545680370989647)
    ·
      refine ⟨122627714403818520556484471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81751809602545680370989647 122627714403818520556484471)
      ·
        refine ⟨183941571605727780834726707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122627714403818520556484471 183941571605727780834726707)
        ·
          refine ⟨275912357408591671252090061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183941571605727780834726707 275912357408591671252090061)
          ·
            refine ⟨103467134028221876719533773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275912357408591671252090061 103467134028221876719533773)
            ·
              refine ⟨38800175260583203769825165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103467134028221876719533773 38800175260583203769825165)
              ·
                refine ⟨14550065722718701413684437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38800175260583203769825165 14550065722718701413684437)
                ·
                  refine ⟨341017165376219564383229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14550065722718701413684437 341017165376219564383229)
                  ·
                    rfl

theorem cell23_5977157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 7].length) (baseStart_5977157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977157 prefixEnd_5977157 := by exact prefixLift 5977157
  have htrace : WordTrace (prefixWord ++ tailWord_5977157) baseStart_5977157 baseEnd_5977157 := by
    simpa [prefixWord, tailWord_5977157, baseEnd_5977157] using wordTrace_append hprefix tailTrace_5977157
  have hstable : (prefixWord ++ tailWord_5977157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977157).length < 2 ^ (prefixWord ++ tailWord_5977157).sum := by decide
  have hdescent : baseEnd_5977157 < baseStart_5977157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977191 : List Nat := [1, 1, 5, 1, 1, 3, 3, 3, 5]
def baseStart_5977191 : Nat := 118140960795 + 5977191 * 2 ^ 59
def prefixEnd_5977191 : Nat := 4983230072969 + 3 ^ 40 * 5977191 * 2
def baseEnd_5977191 : Nat := 341019105192025438491545

theorem tailTrace_5977191 : CollatzResearch.WordTrace tailWord_5977191 prefixEnd_5977191 341019105192025438491545 := by
  unfold tailWord_5977191
  simp only [CollatzResearch.WordTrace]
  refine ⟨218006065688665304796043427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145337377125776869864028951 218006065688665304796043427)
  ·
    refine ⟨327009098532997957194065141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218006065688665304796043427 327009098532997957194065141)
    ·
      refine ⟨30657102987468558486943607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 327009098532997957194065141 30657102987468558486943607)
      ·
        refine ⟨45985654481202837730415411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30657102987468558486943607 45985654481202837730415411)
        ·
          refine ⟨68978481721804256595623117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45985654481202837730415411 68978481721804256595623117)
          ·
            refine ⟨25866930645676596223358669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68978481721804256595623117 25866930645676596223358669)
            ·
              refine ⟨9700098992128723583759501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25866930645676596223358669 9700098992128723583759501)
              ·
                refine ⟨3637537122048271343909813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9700098992128723583759501 3637537122048271343909813)
                ·
                  refine ⟨341019105192025438491545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3637537122048271343909813 341019105192025438491545)
                  ·
                    rfl

theorem cell23_5977191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 5].length) (baseStart_5977191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977191 prefixEnd_5977191 := by exact prefixLift 5977191
  have htrace : WordTrace (prefixWord ++ tailWord_5977191) baseStart_5977191 baseEnd_5977191 := by
    simpa [prefixWord, tailWord_5977191, baseEnd_5977191] using wordTrace_append hprefix tailTrace_5977191
  have hstable : (prefixWord ++ tailWord_5977191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977191).length < 2 ^ (prefixWord ++ tailWord_5977191).sum := by decide
  have hdescent : baseEnd_5977191 < baseStart_5977191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977227 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 5]
def baseStart_5977227 : Nat := 118140960795 + 5977227 * 2 ^ 59
def prefixEnd_5977227 : Nat := 4983230072969 + 3 ^ 40 * 5977227 * 2
def baseEnd_5977227 : Nat := 3069190432031790805573739

theorem tailTrace_5977227 : CollatzResearch.WordTrace tailWord_5977227 prefixEnd_5977227 3069190432031790805573739 := by
  unfold tailWord_5977227
  simp only [CollatzResearch.WordTrace]
  refine ⟨218007378716534882944353935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145338252477689921962902623 218007378716534882944353935)
  ·
    refine ⟨327011068074802324416530903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218007378716534882944353935 327011068074802324416530903)
    ·
      refine ⟨490516602112203486624796355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327011068074802324416530903 490516602112203486624796355)
      ·
        refine ⟨735774903168305229937194533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490516602112203486624796355 735774903168305229937194533)
        ·
          refine ⟨137957794344057230613223975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 735774903168305229937194533 137957794344057230613223975)
          ·
            refine ⟨206936691516085845919835963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137957794344057230613223975 206936691516085845919835963)
            ·
              refine ⟨310405037274128768879753945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206936691516085845919835963 310405037274128768879753945)
              ·
                refine ⟨232803777955596576659815459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310405037274128768879753945 232803777955596576659815459)
                ·
                  refine ⟨349205666933394864989723189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232803777955596576659815459 349205666933394864989723189)
                  ·
                    refine ⟨32738031275005768592786549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 349205666933394864989723189 32738031275005768592786549)
                    ·
                      refine ⟨3069190432031790805573739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32738031275005768592786549 3069190432031790805573739)
                      ·
                        rfl

theorem cell23_5977227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 5].length) (baseStart_5977227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977227 prefixEnd_5977227 := by exact prefixLift 5977227
  have htrace : WordTrace (prefixWord ++ tailWord_5977227) baseStart_5977227 baseEnd_5977227 := by
    simpa [prefixWord, tailWord_5977227, baseEnd_5977227] using wordTrace_append hprefix tailTrace_5977227
  have hstable : (prefixWord ++ tailWord_5977227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977227).length < 2 ^ (prefixWord ++ tailWord_5977227).sum := by decide
  have hdescent : baseEnd_5977227 < baseStart_5977227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977257 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 7]
def baseStart_5977257 : Nat := 118140960795 + 5977257 * 2 ^ 59
def prefixEnd_5977257 : Nat := 4983230072969 + 3 ^ 40 * 5977257 * 2
def baseEnd_5977257 : Nat := 3069205836451425688198601

theorem tailTrace_5977257 : CollatzResearch.WordTrace tailWord_5977257 prefixEnd_5977257 3069205836451425688198601 := by
  unfold tailWord_5977257
  simp only [CollatzResearch.WordTrace]
  refine ⟨218008472906426198067946025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145338981937617465378630683 218008472906426198067946025)
  ·
    refine ⟨163506354679819648550959519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218008472906426198067946025 163506354679819648550959519)
    ·
      refine ⟨245259532019729472826439279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163506354679819648550959519 245259532019729472826439279)
      ·
        refine ⟨367889298029594209239658919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245259532019729472826439279 367889298029594209239658919)
        ·
          refine ⟨551833947044391313859488379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367889298029594209239658919 551833947044391313859488379)
          ·
            refine ⟨827750920566586970789232569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551833947044391313859488379 827750920566586970789232569)
            ·
              refine ⟨620813190424940228091924427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 827750920566586970789232569 620813190424940228091924427)
              ·
                refine ⟨931219785637410342137886641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620813190424940228091924427 931219785637410342137886641)
                ·
                  refine ⟨698414839228057756603414981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 931219785637410342137886641 698414839228057756603414981)
                  ·
                    refine ⟨130952782355260829363140309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 698414839228057756603414981 130952782355260829363140309)
                    ·
                      refine ⟨3069205836451425688198601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130952782355260829363140309 3069205836451425688198601)
                      ·
                        rfl

theorem cell23_5977257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_5977257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977257 prefixEnd_5977257 := by exact prefixLift 5977257
  have htrace : WordTrace (prefixWord ++ tailWord_5977257) baseStart_5977257 baseEnd_5977257 := by
    simpa [prefixWord, tailWord_5977257, baseEnd_5977257] using wordTrace_append hprefix tailTrace_5977257
  have hstable : (prefixWord ++ tailWord_5977257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977257).length < 2 ^ (prefixWord ++ tailWord_5977257).sum := by decide
  have hdescent : baseEnd_5977257 < baseStart_5977257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977258 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_5977258 : Nat := 118140960795 + 5977258 * 2 ^ 59
def prefixEnd_5977258 : Nat := 4983230072969 + 3 ^ 40 * 5977258 * 2
def baseEnd_5977258 : Nat := 3069206349932080184286097

theorem tailTrace_5977258 : CollatzResearch.WordTrace tailWord_5977258 prefixEnd_5977258 3069206349932080184286097 := by
  unfold tailWord_5977258
  simp only [CollatzResearch.WordTrace]
  refine ⟨54502127344855643809683107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145339006252948383492488285 54502127344855643809683107)
  ·
    refine ⟨81753191017283465714524661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54502127344855643809683107 81753191017283465714524661)
    ·
      refine ⟨7664361657870324910736687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81753191017283465714524661 7664361657870324910736687)
      ·
        refine ⟨11496542486805487366105031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7664361657870324910736687 11496542486805487366105031)
        ·
          refine ⟨17244813730208231049157547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11496542486805487366105031 17244813730208231049157547)
          ·
            refine ⟨25867220595312346573736321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17244813730208231049157547 25867220595312346573736321)
            ·
              refine ⟨19400415446484259930302241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25867220595312346573736321 19400415446484259930302241)
              ·
                refine ⟨14550311584863194947726681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19400415446484259930302241 14550311584863194947726681)
                ·
                  refine ⟨10912733688647396210795011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14550311584863194947726681 10912733688647396210795011)
                  ·
                    refine ⟨16369100532971094316192517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10912733688647396210795011 16369100532971094316192517)
                    ·
                      refine ⟨3069206349932080184286097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16369100532971094316192517 3069206349932080184286097)
                      ·
                        rfl

theorem cell23_5977258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_5977258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977258 prefixEnd_5977258 := by exact prefixLift 5977258
  have htrace : WordTrace (prefixWord ++ tailWord_5977258) baseStart_5977258 baseEnd_5977258 := by
    simpa [prefixWord, tailWord_5977258, baseEnd_5977258] using wordTrace_append hprefix tailTrace_5977258
  have hstable : (prefixWord ++ tailWord_5977258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977258).length < 2 ^ (prefixWord ++ tailWord_5977258).sum := by decide
  have hdescent : baseEnd_5977258 < baseStart_5977258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977274 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3]
def baseStart_5977274 : Nat := 118140960795 + 5977274 * 2 ^ 59
def prefixEnd_5977274 : Nat := 4983230072969 + 3 ^ 40 * 5977274 * 2
def baseEnd_5977274 : Nat := 3069214565622552121686023

theorem tailTrace_5977274 : CollatzResearch.WordTrace tailWord_5977274 prefixEnd_5977274 3069214565622552121686023 := by
  unfold tailWord_5977274
  simp only [CollatzResearch.WordTrace]
  refine ⟨54502273236841152492828719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145339395298243073314209917 54502273236841152492828719)
  ·
    refine ⟨81753409855261728739243079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54502273236841152492828719 81753409855261728739243079)
    ·
      refine ⟨122630114782892593108864619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81753409855261728739243079 122630114782892593108864619)
      ·
        refine ⟨183945172174338889663296929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122630114782892593108864619 183945172174338889663296929)
        ·
          refine ⟨137958879130754167247472697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183945172174338889663296929 137958879130754167247472697)
          ·
            refine ⟨103469159348065625435604523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137958879130754167247472697 103469159348065625435604523)
            ·
              refine ⟨155203739022098438153406785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103469159348065625435604523 155203739022098438153406785)
              ·
                refine ⟨116402804266573828615055089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155203739022098438153406785 116402804266573828615055089)
                ·
                  refine ⟨87302103199930371461291317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116402804266573828615055089 87302103199930371461291317)
                  ·
                    refine ⟨8184572174993472324496061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87302103199930371461291317 8184572174993472324496061)
                    ·
                      refine ⟨3069214565622552121686023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8184572174993472324496061 3069214565622552121686023)
                      ·
                        rfl

theorem cell23_5977274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_5977274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977274 prefixEnd_5977274 := by exact prefixLift 5977274
  have htrace : WordTrace (prefixWord ++ tailWord_5977274) baseStart_5977274 baseEnd_5977274 := by
    simpa [prefixWord, tailWord_5977274, baseEnd_5977274] using wordTrace_append hprefix tailTrace_5977274
  have hstable : (prefixWord ++ tailWord_5977274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977274).length < 2 ^ (prefixWord ++ tailWord_5977274).sum := by decide
  have hdescent : baseEnd_5977274 < baseStart_5977274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977325 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_5977325 : Nat := 118140960795 + 5977325 * 2 ^ 59
def prefixEnd_5977325 : Nat := 4983230072969 + 3 ^ 40 * 5977325 * 2
def baseEnd_5977325 : Nat := 3069240753135931422148289

theorem tailTrace_5977325 : CollatzResearch.WordTrace tailWord_5977325 prefixEnd_5977325 3069240753135931422148289 := by
  unfold tailWord_5977325
  simp only [CollatzResearch.WordTrace]
  refine ⟨218010953070179845681421429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145340635380119897120947619 218010953070179845681421429)
  ·
    refine ⟨20438526850329360532633259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218010953070179845681421429 20438526850329360532633259)
    ·
      refine ⟨30657790275494040798949889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20438526850329360532633259 30657790275494040798949889)
      ·
        refine ⟨22993342706620530599212417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30657790275494040798949889 22993342706620530599212417)
        ·
          refine ⟨17245007029965397949409313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22993342706620530599212417 17245007029965397949409313)
          ·
            refine ⟨12933755272474048462056985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17245007029965397949409313 12933755272474048462056985)
            ·
              refine ⟨9700316454355536346542739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12933755272474048462056985 9700316454355536346542739)
              ·
                refine ⟨14550474681533304519814109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9700316454355536346542739 14550474681533304519814109)
                ·
                  refine ⟨5456428005574989194930291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14550474681533304519814109 5456428005574989194930291)
                  ·
                    refine ⟨8184642008362483792395437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5456428005574989194930291 8184642008362483792395437)
                    ·
                      refine ⟨3069240753135931422148289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8184642008362483792395437 3069240753135931422148289)
                      ·
                        rfl

theorem cell23_5977325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_5977325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977325 prefixEnd_5977325 := by exact prefixLift 5977325
  have htrace : WordTrace (prefixWord ++ tailWord_5977325) baseStart_5977325 baseEnd_5977325 := by
    simpa [prefixWord, tailWord_5977325, baseEnd_5977325] using wordTrace_append hprefix tailTrace_5977325
  have hstable : (prefixWord ++ tailWord_5977325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977325).length < 2 ^ (prefixWord ++ tailWord_5977325).sum := by decide
  have hdescent : baseEnd_5977325 < baseStart_5977325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977348 : List Nat := [2, 3, 2, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_5977348 : Nat := 118140960795 + 5977348 * 2 ^ 59
def prefixEnd_5977348 : Nat := 4983230072969 + 3 ^ 40 * 5977348 * 2
def baseEnd_5977348 : Nat := 3069252563190984832160683

theorem tailTrace_5977348 : CollatzResearch.WordTrace tailWord_5977348 prefixEnd_5977348 3069252563190984832160683 := by
  unfold tailWord_5977348
  simp only [CollatzResearch.WordTrace]
  refine ⟨109005895974548260304754349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145341194632731013739672465 109005895974548260304754349)
  ·
    refine ⟨40877210990455597614282881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109005895974548260304754349 40877210990455597614282881)
    ·
      refine ⟨30657908242841698210712161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40877210990455597614282881 30657908242841698210712161)
      ·
        refine ⟨22993431182131273658034121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30657908242841698210712161 22993431182131273658034121)
        ·
          refine ⟨17245073386598455243525591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22993431182131273658034121 17245073386598455243525591)
          ·
            refine ⟨25867610079897682865288387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17245073386598455243525591 25867610079897682865288387)
            ·
              refine ⟨38801415119846524297932581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25867610079897682865288387 38801415119846524297932581)
              ·
                refine ⟨7275265334971223305862359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38801415119846524297932581 7275265334971223305862359)
                ·
                  refine ⟨10912898002456834958793539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7275265334971223305862359 10912898002456834958793539)
                  ·
                    refine ⟨16369347003685252438190309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10912898002456834958793539 16369347003685252438190309)
                    ·
                      refine ⟨3069252563190984832160683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16369347003685252438190309 3069252563190984832160683)
                      ·
                        rfl

theorem cell23_5977348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_5977348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977348 prefixEnd_5977348 := by exact prefixLift 5977348
  have htrace : WordTrace (prefixWord ++ tailWord_5977348) baseStart_5977348 baseEnd_5977348 := by
    simpa [prefixWord, tailWord_5977348, baseEnd_5977348] using wordTrace_append hprefix tailTrace_5977348
  have hstable : (prefixWord ++ tailWord_5977348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977348).length < 2 ^ (prefixWord ++ tailWord_5977348).sum := by decide
  have hdescent : baseEnd_5977348 < baseStart_5977348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977368 : List Nat := [2, 1, 2, 3, 1, 3, 2, 3, 1, 2, 3]
def baseStart_5977368 : Nat := 118140960795 + 5977368 * 2 ^ 59
def prefixEnd_5977368 : Nat := 4983230072969 + 3 ^ 40 * 5977368 * 2
def baseEnd_5977368 : Nat := 3069262832804074753910591

theorem tailTrace_5977368 : CollatzResearch.WordTrace tailWord_5977368 prefixEnd_5977368 3069262832804074753910591 := by
  unfold tailWord_5977368
  simp only [CollatzResearch.WordTrace]
  refine ⟨109006260704512032012618379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145341680939349376016824505 109006260704512032012618379)
  ·
    refine ⟨163509391056768048018927569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109006260704512032012618379 163509391056768048018927569)
    ·
      refine ⟨122632043292576036014195677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163509391056768048018927569 122632043292576036014195677)
      ·
        refine ⟨45987016234716013505323379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122632043292576036014195677 45987016234716013505323379)
        ·
          refine ⟨68980524352074020257985069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45987016234716013505323379 68980524352074020257985069)
          ·
            refine ⟨25867696632027757596744401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68980524352074020257985069 25867696632027757596744401)
            ·
              refine ⟨19400772474020818197558301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25867696632027757596744401 19400772474020818197558301)
              ·
                refine ⟨7275289677757806824084363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19400772474020818197558301 7275289677757806824084363)
                ·
                  refine ⟨10912934516636710236126545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7275289677757806824084363 10912934516636710236126545)
                  ·
                    refine ⟨8184700887477532677094909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10912934516636710236126545 8184700887477532677094909)
                    ·
                      refine ⟨3069262832804074753910591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8184700887477532677094909 3069262832804074753910591)
                      ·
                        rfl

theorem cell23_5977368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_5977368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977368 prefixEnd_5977368 := by exact prefixLift 5977368
  have htrace : WordTrace (prefixWord ++ tailWord_5977368) baseStart_5977368 baseEnd_5977368 := by
    simpa [prefixWord, tailWord_5977368, baseEnd_5977368] using wordTrace_append hprefix tailTrace_5977368
  have hstable : (prefixWord ++ tailWord_5977368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977368).length < 2 ^ (prefixWord ++ tailWord_5977368).sum := by decide
  have hdescent : baseEnd_5977368 < baseStart_5977368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977391 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 2, 7, 2]
def baseStart_5977391 : Nat := 118140960795 + 5977391 * 2 ^ 59
def prefixEnd_5977391 : Nat := 4983230072969 + 3 ^ 40 * 5977391 * 2
def baseEnd_5977391 : Nat := 3069274642859128163922985

theorem tailTrace_5977391 : CollatzResearch.WordTrace tailWord_5977391 prefixEnd_5977391 3069274642859128163922985 := by
  unfold tailWord_5977391
  simp only [CollatzResearch.WordTrace]
  refine ⟨218013360287940738953324027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145342240191960492635549351 218013360287940738953324027)
  ·
    refine ⟨327020040431911108429986041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218013360287940738953324027 327020040431911108429986041)
    ·
      refine ⟨245265030323933331322489531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327020040431911108429986041 245265030323933331322489531)
      ·
        refine ⟨367897545485899996983734297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245265030323933331322489531 367897545485899996983734297)
        ·
          refine ⟨275923159114424997737800723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367897545485899996983734297 275923159114424997737800723)
          ·
            refine ⟨413884738671637496606701085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275923159114424997737800723 413884738671637496606701085)
            ·
              refine ⟨155206777001864061227512907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 413884738671637496606701085 155206777001864061227512907)
              ·
                refine ⟨232810165502796091841269361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155206777001864061227512907 232810165502796091841269361)
                ·
                  refine ⟨174607624127097068880952021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232810165502796091841269361 174607624127097068880952021)
                  ·
                    refine ⟨4092366190478837551897313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 174607624127097068880952021 4092366190478837551897313)
                    ·
                      refine ⟨3069274642859128163922985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4092366190478837551897313 3069274642859128163922985)
                      ·
                        rfl

theorem cell23_5977391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 7, 2].length) (baseStart_5977391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977391 prefixEnd_5977391 := by exact prefixLift 5977391
  have htrace : WordTrace (prefixWord ++ tailWord_5977391) baseStart_5977391 baseEnd_5977391 := by
    simpa [prefixWord, tailWord_5977391, baseEnd_5977391] using wordTrace_append hprefix tailTrace_5977391
  have hstable : (prefixWord ++ tailWord_5977391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977391).length < 2 ^ (prefixWord ++ tailWord_5977391).sum := by decide
  have hdescent : baseEnd_5977391 < baseStart_5977391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977408 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 3, 3, 2]
def baseStart_5977408 : Nat := 118140960795 + 5977408 * 2 ^ 59
def prefixEnd_5977408 : Nat := 4983230072969 + 3 ^ 40 * 5977408 * 2
def baseEnd_5977408 : Nat := 3069283372030254597410407

theorem tailTrace_5977408 : CollatzResearch.WordTrace tailWord_5977408 prefixEnd_5977408 3069283372030254597410407 := by
  unfold tailWord_5977408
  simp only [CollatzResearch.WordTrace]
  refine ⟨109006990164439575428346439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145342653552586100571128585 109006990164439575428346439)
  ·
    refine ⟨163510485246659363142519659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109006990164439575428346439 163510485246659363142519659)
    ·
      refine ⟨245265727869989044713779489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163510485246659363142519659 245265727869989044713779489)
      ·
        refine ⟨183949295902491783535334617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245265727869989044713779489 183949295902491783535334617)
        ·
          refine ⟨137961971926868837651500963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183949295902491783535334617 137961971926868837651500963)
          ·
            refine ⟨206942957890303256477251445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137961971926868837651500963 206942957890303256477251445)
            ·
              refine ⟨19400902302215930294742323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 206942957890303256477251445 19400902302215930294742323)
              ·
                refine ⟨29101353453323895442113485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19400902302215930294742323 29101353453323895442113485)
                ·
                  refine ⟨10913007544996460790792557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29101353453323895442113485 10913007544996460790792557)
                  ·
                    refine ⟨4092377829373672796547209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10913007544996460790792557 4092377829373672796547209)
                    ·
                      refine ⟨3069283372030254597410407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4092377829373672796547209 3069283372030254597410407)
                      ·
                        rfl

theorem cell23_5977408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 3, 3, 2].length) (baseStart_5977408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977408 prefixEnd_5977408 := by exact prefixLift 5977408
  have htrace : WordTrace (prefixWord ++ tailWord_5977408) baseStart_5977408 baseEnd_5977408 := by
    simpa [prefixWord, tailWord_5977408, baseEnd_5977408] using wordTrace_append hprefix tailTrace_5977408
  have hstable : (prefixWord ++ tailWord_5977408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977408).length < 2 ^ (prefixWord ++ tailWord_5977408).sum := by decide
  have hdescent : baseEnd_5977408 < baseStart_5977408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977448 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 2, 6]
def baseStart_5977448 : Nat := 118140960795 + 5977448 * 2 ^ 59
def prefixEnd_5977448 : Nat := 4983230072969 + 3 ^ 40 * 5977448 * 2
def baseEnd_5977448 : Nat := 1023101303752144813636741

theorem tailTrace_5977448 : CollatzResearch.WordTrace tailWord_5977448 prefixEnd_5977448 1023101303752144813636741 := by
  unfold tailWord_5977448
  simp only [CollatzResearch.WordTrace]
  refine ⟨109007719624367118844074499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145343626165822825125432665 109007719624367118844074499)
  ·
    refine ⟨163511579436550678266111749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109007719624367118844074499 163511579436550678266111749)
    ·
      refine ⟨30658421144353252174895953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163511579436550678266111749 30658421144353252174895953)
      ·
        refine ⟨22993815858264939131171965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30658421144353252174895953 22993815858264939131171965)
        ·
          refine ⟨8622680946849352174189487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22993815858264939131171965 8622680946849352174189487)
          ·
            refine ⟨12934021420274028261284231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8622680946849352174189487 12934021420274028261284231)
            ·
              refine ⟨19401032130411042391926347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12934021420274028261284231 19401032130411042391926347)
              ·
                refine ⟨29101548195616563587889521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19401032130411042391926347 29101548195616563587889521)
                ·
                  refine ⟨21826161146712422690917141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29101548195616563587889521 21826161146712422690917141)
                  ·
                    refine ⟨1023101303752144813636741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21826161146712422690917141 1023101303752144813636741)
                    ·
                      rfl

theorem cell23_5977448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_5977448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977448 prefixEnd_5977448 := by exact prefixLift 5977448
  have htrace : WordTrace (prefixWord ++ tailWord_5977448) baseStart_5977448 baseEnd_5977448 := by
    simpa [prefixWord, tailWord_5977448, baseEnd_5977448] using wordTrace_append hprefix tailTrace_5977448
  have hstable : (prefixWord ++ tailWord_5977448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977448).length < 2 ^ (prefixWord ++ tailWord_5977448).sum := by decide
  have hdescent : baseEnd_5977448 < baseStart_5977448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977455 : List Nat := [1, 1, 2, 1, 3, 1, 3, 5, 2, 2, 2]
def baseStart_5977455 : Nat := 118140960795 + 5977455 * 2 ^ 59
def prefixEnd_5977455 : Nat := 4983230072969 + 3 ^ 40 * 5977455 * 2
def baseEnd_5977455 : Nat := 3069307505621015913522691

theorem tailTrace_5977455 : CollatzResearch.WordTrace tailWord_5977455 prefixEnd_5977455 3069307505621015913522691 := by
  unfold tailWord_5977455
  simp only [CollatzResearch.WordTrace]
  refine ⟨218015694559708877883653819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145343796373139251922435879 218015694559708877883653819)
  ·
    refine ⟨327023541839563316825480729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218015694559708877883653819 327023541839563316825480729)
    ·
      refine ⟨245267656379672487619110547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327023541839563316825480729 245267656379672487619110547)
      ·
        refine ⟨367901484569508731428665821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245267656379672487619110547 367901484569508731428665821)
        ·
          refine ⟨137963056713565774285749683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367901484569508731428665821 137963056713565774285749683)
          ·
            refine ⟨206944585070348661428624525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137963056713565774285749683 206944585070348661428624525)
            ·
              refine ⟨77604219401380748035734197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206944585070348661428624525 77604219401380748035734197)
              ·
                refine ⟨7275395568879445128350081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77604219401380748035734197 7275395568879445128350081)
                ·
                  refine ⟨5456546676659583846262561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7275395568879445128350081 5456546676659583846262561)
                  ·
                    refine ⟨4092410007494687884696921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5456546676659583846262561 4092410007494687884696921)
                    ·
                      refine ⟨3069307505621015913522691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4092410007494687884696921 3069307505621015913522691)
                      ·
                        rfl

theorem cell23_5977455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 2, 2].length) (baseStart_5977455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977455 prefixEnd_5977455 := by exact prefixLift 5977455
  have htrace : WordTrace (prefixWord ++ tailWord_5977455) baseStart_5977455 baseEnd_5977455 := by
    simpa [prefixWord, tailWord_5977455, baseEnd_5977455] using wordTrace_append hprefix tailTrace_5977455
  have hstable : (prefixWord ++ tailWord_5977455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977455).length < 2 ^ (prefixWord ++ tailWord_5977455).sum := by decide
  have hdescent : baseEnd_5977455 < baseStart_5977455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977471 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 3]
def baseStart_5977471 : Nat := 118140960795 + 5977471 * 2 ^ 59
def prefixEnd_5977471 : Nat := 4983230072969 + 3 ^ 40 * 5977471 * 2
def baseEnd_5977471 : Nat := 3069315721311487850922617

theorem tailTrace_5977471 : CollatzResearch.WordTrace tailWord_5977471 prefixEnd_5977471 3069315721311487850922617 := by
  unfold tailWord_5977471
  simp only [CollatzResearch.WordTrace]
  refine ⟨218016278127650912616236267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145344185418433941744157511 218016278127650912616236267)
  ·
    refine ⟨327024417191476368924354401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218016278127650912616236267 327024417191476368924354401)
    ·
      refine ⟨245268312893607276693265801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327024417191476368924354401 245268312893607276693265801)
      ·
        refine ⟨183951234670205457519949351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245268312893607276693265801 183951234670205457519949351)
        ·
          refine ⟨275926852005308186279924027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183951234670205457519949351 275926852005308186279924027)
          ·
            refine ⟨413890278007962279419886041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275926852005308186279924027 413890278007962279419886041)
            ·
              refine ⟨310417708505971709564914531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413890278007962279419886041 310417708505971709564914531)
              ·
                refine ⟨465626562758957564347371797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310417708505971709564914531 465626562758957564347371797)
                ·
                  refine ⟨21826245129326135828783053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 465626562758957564347371797 21826245129326135828783053)
                  ·
                    refine ⟨8184841923497300935793645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21826245129326135828783053 8184841923497300935793645)
                    ·
                      refine ⟨3069315721311487850922617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8184841923497300935793645 3069315721311487850922617)
                      ·
                        rfl

theorem cell23_5977471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_5977471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977471 prefixEnd_5977471 := by exact prefixLift 5977471
  have htrace : WordTrace (prefixWord ++ tailWord_5977471) baseStart_5977471 baseEnd_5977471 := by
    simpa [prefixWord, tailWord_5977471, baseEnd_5977471] using wordTrace_append hprefix tailTrace_5977471
  have hstable : (prefixWord ++ tailWord_5977471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977471).length < 2 ^ (prefixWord ++ tailWord_5977471).sum := by decide
  have hdescent : baseEnd_5977471 < baseStart_5977471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977521 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 2, 8]
def baseStart_5977521 : Nat := 118140960795 + 5977521 * 2 ^ 59
def prefixEnd_5977521 : Nat := 4983230072969 + 3 ^ 40 * 5977521 * 2
def baseEnd_5977521 : Nat := 1023113798448070885099129

theorem tailTrace_5977521 : CollatzResearch.WordTrace tailWord_5977521 prefixEnd_5977521 1023113798448070885099129 := by
  unfold tailWord_5977521
  simp only [CollatzResearch.WordTrace]
  refine ⟨218018101777469771155556417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145345401184979847437037611 218018101777469771155556417)
  ·
    refine ⟨163513576333102328366667313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218018101777469771155556417 163513576333102328366667313)
    ·
      refine ⟨122635182249826746275000485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163513576333102328366667313 122635182249826746275000485)
      ·
        refine ⟨22994096671842514926562591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122635182249826746275000485 22994096671842514926562591)
        ·
          refine ⟨34491145007763772389843887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22994096671842514926562591 34491145007763772389843887)
          ·
            refine ⟨51736717511645658584765831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34491145007763772389843887 51736717511645658584765831)
            ·
              refine ⟨77605076267468487877148747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51736717511645658584765831 77605076267468487877148747)
              ·
                refine ⟨116407614401202731815723121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77605076267468487877148747 116407614401202731815723121)
                ·
                  refine ⟨87305710800902048861792341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116407614401202731815723121 87305710800902048861792341)
                  ·
                    refine ⟨1023113798448070885099129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87305710800902048861792341 1023113798448070885099129)
                    ·
                      rfl

theorem cell23_5977521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_5977521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977521 prefixEnd_5977521 := by exact prefixLift 5977521
  have htrace : WordTrace (prefixWord ++ tailWord_5977521) baseStart_5977521 baseEnd_5977521 := by
    simpa [prefixWord, tailWord_5977521, baseEnd_5977521] using wordTrace_append hprefix tailTrace_5977521
  have hstable : (prefixWord ++ tailWord_5977521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977521).length < 2 ^ (prefixWord ++ tailWord_5977521).sum := by decide
  have hdescent : baseEnd_5977521 < baseStart_5977521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977528 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 1, 6, 2]
def baseStart_5977528 : Nat := 118140960795 + 5977528 * 2 ^ 59
def prefixEnd_5977528 : Nat := 4983230072969 + 3 ^ 40 * 5977528 * 2
def baseEnd_5977528 : Nat := 3069344989708794127909855

theorem tailTrace_5977528 : CollatzResearch.WordTrace tailWord_5977528 prefixEnd_5977528 3069344989708794127909855 := by
  unfold tailWord_5977528
  simp only [CollatzResearch.WordTrace]
  refine ⟨109009178544222205675530619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145345571392296274234040825 109009178544222205675530619)
  ·
    refine ⟨163513767816333308513295929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109009178544222205675530619 163513767816333308513295929)
    ·
      refine ⟨122635325862249981384971947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163513767816333308513295929 122635325862249981384971947)
      ·
        refine ⟨183952988793374972077457921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122635325862249981384971947 183952988793374972077457921)
        ·
          refine ⟨137964741595031229058093441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183952988793374972077457921 137964741595031229058093441)
          ·
            refine ⟨103473556196273421793570081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137964741595031229058093441 103473556196273421793570081)
            ·
              refine ⟨77605167147205066345177561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103473556196273421793570081 77605167147205066345177561)
              ·
                refine ⟨58203875360403799758883171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77605167147205066345177561 58203875360403799758883171)
                ·
                  refine ⟨87305813040605699638324757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58203875360403799758883171 87305813040605699638324757)
                  ·
                    refine ⟨4092459986278392170546473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87305813040605699638324757 4092459986278392170546473)
                    ·
                      refine ⟨3069344989708794127909855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4092459986278392170546473 3069344989708794127909855)
                      ·
                        rfl

theorem cell23_5977528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 6, 2].length) (baseStart_5977528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977528 prefixEnd_5977528 := by exact prefixLift 5977528
  have htrace : WordTrace (prefixWord ++ tailWord_5977528) baseStart_5977528 baseEnd_5977528 := by
    simpa [prefixWord, tailWord_5977528, baseEnd_5977528] using wordTrace_append hprefix tailTrace_5977528
  have hstable : (prefixWord ++ tailWord_5977528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977528).length < 2 ^ (prefixWord ++ tailWord_5977528).sum := by decide
  have hdescent : baseEnd_5977528 < baseStart_5977528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977551 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 8]
def baseStart_5977551 : Nat := 118140960795 + 5977551 * 2 ^ 59
def prefixEnd_5977551 : Nat := 4983230072969 + 3 ^ 40 * 5977551 * 2
def baseEnd_5977551 : Nat := 341039644418205281991361

theorem tailTrace_5977551 : CollatzResearch.WordTrace tailWord_5977551 prefixEnd_5977551 341039644418205281991361 := by
  unfold tailWord_5977551
  simp only [CollatzResearch.WordTrace]
  refine ⟨218019195967361086279148507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145346130644907390852765671 218019195967361086279148507)
  ·
    refine ⟨327028793951041629418722761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218019195967361086279148507 327028793951041629418722761)
    ·
      refine ⟨245271595463281222064042071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327028793951041629418722761 245271595463281222064042071)
      ·
        refine ⟨367907393194921833096063107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245271595463281222064042071 367907393194921833096063107)
        ·
          refine ⟨551861089792382749644094661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367907393194921833096063107 551861089792382749644094661)
          ·
            refine ⟨103473954336071765558267749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 551861089792382749644094661 103473954336071765558267749)
            ·
              refine ⟨19401366438013456042175203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103473954336071765558267749 19401366438013456042175203)
              ·
                refine ⟨29102049657020184063262805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19401366438013456042175203 29102049657020184063262805)
                ·
                  refine ⟨341039644418205281991361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29102049657020184063262805 341039644418205281991361)
                  ·
                    rfl

theorem cell23_5977551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 8].length) (baseStart_5977551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977551 prefixEnd_5977551 := by exact prefixLift 5977551
  have htrace : WordTrace (prefixWord ++ tailWord_5977551) baseStart_5977551 baseEnd_5977551 := by
    simpa [prefixWord, tailWord_5977551, baseEnd_5977551] using wordTrace_append hprefix tailTrace_5977551
  have hstable : (prefixWord ++ tailWord_5977551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977551).length < 2 ^ (prefixWord ++ tailWord_5977551).sum := by decide
  have hdescent : baseEnd_5977551 < baseStart_5977551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977591 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 5]
def baseStart_5977591 : Nat := 118140960795 + 5977591 * 2 ^ 59
def prefixEnd_5977591 : Nat := 4983230072969 + 3 ^ 40 * 5977591 * 2
def baseEnd_5977591 : Nat := 3069377338990027381422065

theorem tailTrace_5977591 : CollatzResearch.WordTrace tailWord_5977591 prefixEnd_5977591 3069377338990027381422065 := by
  unfold tailWord_5977591
  simp only [CollatzResearch.WordTrace]
  refine ⟨218020654887216173110604627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145347103258144115407069751 218020654887216173110604627)
  ·
    refine ⟨327030982330824259665906941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218020654887216173110604627 327030982330824259665906941)
    ·
      refine ⟨122636618374059097374715103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327030982330824259665906941 122636618374059097374715103)
      ·
        refine ⟨183954927561088646062072655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122636618374059097374715103 183954927561088646062072655)
        ·
          refine ⟨275932391341632969093108983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183954927561088646062072655 275932391341632969093108983)
          ·
            refine ⟨413898587012449453639663475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275932391341632969093108983 413898587012449453639663475)
            ·
              refine ⟨620847880518674180459495213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413898587012449453639663475 620847880518674180459495213)
              ·
                refine ⟨232817955194502817672310705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 620847880518674180459495213 232817955194502817672310705)
                ·
                  refine ⟨174613466395877113254233029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232817955194502817672310705 174613466395877113254233029)
                  ·
                    refine ⟨32740024949226958735168693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 174613466395877113254233029 32740024949226958735168693)
                    ·
                      refine ⟨3069377338990027381422065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32740024949226958735168693 3069377338990027381422065)
                      ·
                        rfl

theorem cell23_5977591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_5977591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977591 prefixEnd_5977591 := by exact prefixLift 5977591
  have htrace : WordTrace (prefixWord ++ tailWord_5977591) baseStart_5977591 baseEnd_5977591 := by
    simpa [prefixWord, tailWord_5977591, baseEnd_5977591] using wordTrace_append hprefix tailTrace_5977591
  have hstable : (prefixWord ++ tailWord_5977591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977591).length < 2 ^ (prefixWord ++ tailWord_5977591).sum := by decide
  have hdescent : baseEnd_5977591 < baseStart_5977591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977602 : List Nat := [3, 4, 1, 2, 1, 2, 2, 2, 6]
def baseStart_5977602 : Nat := 118140960795 + 5977602 * 2 ^ 59
def prefixEnd_5977602 : Nat := 4983230072969 + 3 ^ 40 * 5977602 * 2
def baseEnd_5977602 : Nat := 341042554141914093153835

theorem tailTrace_5977602 : CollatzResearch.WordTrace tailWord_5977602 prefixEnd_5977602 341042554141914093153835 := by
  unfold tailWord_5977602
  simp only [CollatzResearch.WordTrace]
  refine ⟨54505264022544080497313765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145347370726784214659503373 54505264022544080497313765)
  ·
    refine ⟨10219737004227015093246331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54505264022544080497313765 10219737004227015093246331)
    ·
      refine ⟨15329605506340522639869497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10219737004227015093246331 15329605506340522639869497)
      ·
        refine ⟨11497204129755391979902123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15329605506340522639869497 11497204129755391979902123)
        ·
          refine ⟨17245806194633087969853185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11497204129755391979902123 17245806194633087969853185)
          ·
            refine ⟨12934354645974815977389889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17245806194633087969853185 12934354645974815977389889)
            ·
              refine ⟨9700765984481111983042417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12934354645974815977389889 9700765984481111983042417)
              ·
                refine ⟨7275574488360833987281813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9700765984481111983042417 7275574488360833987281813)
                ·
                  refine ⟨341042554141914093153835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7275574488360833987281813 341042554141914093153835)
                  ·
                    rfl

theorem cell23_5977602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_5977602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977602 prefixEnd_5977602 := by exact prefixLift 5977602
  have htrace : WordTrace (prefixWord ++ tailWord_5977602) baseStart_5977602 baseEnd_5977602 := by
    simpa [prefixWord, tailWord_5977602, baseEnd_5977602] using wordTrace_append hprefix tailTrace_5977602
  have hstable : (prefixWord ++ tailWord_5977602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977602).length < 2 ^ (prefixWord ++ tailWord_5977602).sum := by decide
  have hdescent : baseEnd_5977602 < baseStart_5977602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977646 : List Nat := [4, 1, 3, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_5977646 : Nat := 118140960795 + 5977646 * 2 ^ 59
def prefixEnd_5977646 : Nat := 4983230072969 + 3 ^ 40 * 5977646 * 2
def baseEnd_5977646 : Nat := 3069405580426024666234313

theorem tailTrace_5977646 : CollatzResearch.WordTrace tailWord_5977646 prefixEnd_5977646 3069405580426024666234313 := by
  unfold tailWord_5977646
  simp only [CollatzResearch.WordTrace]
  refine ⟨27252832612752114687982099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145348440601344611669237861 27252832612752114687982099)
  ·
    refine ⟨40879248919128172031973149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27252832612752114687982099 40879248919128172031973149)
    ·
      refine ⟨15329718344673064511989931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40879248919128172031973149 15329718344673064511989931)
      ·
        refine ⟨22994577517009596767984897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15329718344673064511989931 22994577517009596767984897)
        ·
          refine ⟨17245933137757197575988673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22994577517009596767984897 17245933137757197575988673)
          ·
            refine ⟨12934449853317898181991505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17245933137757197575988673 12934449853317898181991505)
            ·
              refine ⟨9700837389988423636493629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12934449853317898181991505 9700837389988423636493629)
              ·
                refine ⟨3637814021245658863685111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9700837389988423636493629 3637814021245658863685111)
                ·
                  refine ⟨5456721031868488295527667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3637814021245658863685111 5456721031868488295527667)
                  ·
                    refine ⟨8185081547802732443291501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5456721031868488295527667 8185081547802732443291501)
                    ·
                      refine ⟨3069405580426024666234313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8185081547802732443291501 3069405580426024666234313)
                      ·
                        rfl

theorem cell23_5977646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_5977646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977646 prefixEnd_5977646 := by exact prefixLift 5977646
  have htrace : WordTrace (prefixWord ++ tailWord_5977646) baseStart_5977646 baseEnd_5977646 := by
    simpa [prefixWord, tailWord_5977646, baseEnd_5977646] using wordTrace_append hprefix tailTrace_5977646
  have hstable : (prefixWord ++ tailWord_5977646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977646).length < 2 ^ (prefixWord ++ tailWord_5977646).sum := by decide
  have hdescent : baseEnd_5977646 < baseStart_5977646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977669 : List Nat := [1, 3, 1, 1, 1, 4, 1, 6, 1, 2, 2]
def baseStart_5977669 : Nat := 118140960795 + 5977669 * 2 ^ 59
def prefixEnd_5977669 : Nat := 4983230072969 + 3 ^ 40 * 5977669 * 2
def baseEnd_5977669 : Nat := 3069417390481078076246707

theorem tailTrace_5977669 : CollatzResearch.WordTrace tailWord_5977669 prefixEnd_5977669 3069417390481078076246707 := by
  unfold tailWord_5977669
  simp only [CollatzResearch.WordTrace]
  refine ⟨218023499780933592431944061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145348999853955728287962707 218023499780933592431944061)
  ·
    refine ⟨81758812417850097161979023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218023499780933592431944061 81758812417850097161979023)
    ·
      refine ⟨122638218626775145742968535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81758812417850097161979023 122638218626775145742968535)
      ·
        refine ⟨183957327940162718614452803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122638218626775145742968535 183957327940162718614452803)
        ·
          refine ⟨275935991910244077921679205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183957327940162718614452803 275935991910244077921679205)
          ·
            refine ⟨51737998483170764610314851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 275935991910244077921679205 51737998483170764610314851)
            ·
              refine ⟨77606997724756146915472277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51737998483170764610314851 77606997724756146915472277)
              ·
                refine ⟨3637828018347944386662763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77606997724756146915472277 3637828018347944386662763)
                ·
                  refine ⟨5456742027521916579994145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3637828018347944386662763 5456742027521916579994145)
                  ·
                    refine ⟨4092556520641437434995609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5456742027521916579994145 4092556520641437434995609)
                    ·
                      refine ⟨3069417390481078076246707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4092556520641437434995609 3069417390481078076246707)
                      ·
                        rfl

theorem cell23_5977669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 1, 2, 2].length) (baseStart_5977669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977669 prefixEnd_5977669 := by exact prefixLift 5977669
  have htrace : WordTrace (prefixWord ++ tailWord_5977669) baseStart_5977669 baseEnd_5977669 := by
    simpa [prefixWord, tailWord_5977669, baseEnd_5977669] using wordTrace_append hprefix tailTrace_5977669
  have hstable : (prefixWord ++ tailWord_5977669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977669).length < 2 ^ (prefixWord ++ tailWord_5977669).sum := by decide
  have hdescent : baseEnd_5977669 < baseStart_5977669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977682 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_5977682 : Nat := 118140960795 + 5977682 * 2 ^ 59
def prefixEnd_5977682 : Nat := 4983230072969 + 3 ^ 40 * 5977682 * 2
def baseEnd_5977682 : Nat := 3069424065729586525384147

theorem tailTrace_5977682 : CollatzResearch.WordTrace tailWord_5977682 prefixEnd_5977682 3069424065729586525384147 := by
  unfold tailWord_5977682
  simp only [CollatzResearch.WordTrace]
  refine ⟨54505993482471623913041825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145349315953257663768111533 54505993482471623913041825)
  ·
    refine ⟨40879495111853717934781369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54505993482471623913041825 40879495111853717934781369)
    ·
      refine ⟨30659621333890288451086027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40879495111853717934781369 30659621333890288451086027)
      ·
        refine ⟨45989432000835432676629041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30659621333890288451086027 45989432000835432676629041)
        ·
          refine ⟨34492074000626574507471781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45989432000835432676629041 34492074000626574507471781)
          ·
            refine ⟨6467263875117482720150959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34492074000626574507471781 6467263875117482720150959)
            ·
              refine ⟨9700895812676224080226439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6467263875117482720150959 9700895812676224080226439)
              ·
                refine ⟨14551343719014336120339659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9700895812676224080226439 14551343719014336120339659)
                ·
                  refine ⟨21827015578521504180509489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14551343719014336120339659 21827015578521504180509489)
                  ·
                    refine ⟨16370261683891128135382117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21827015578521504180509489 16370261683891128135382117)
                    ·
                      refine ⟨3069424065729586525384147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16370261683891128135382117 3069424065729586525384147)
                      ·
                        rfl

theorem cell23_5977682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_5977682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977682 prefixEnd_5977682 := by exact prefixLift 5977682
  have htrace : WordTrace (prefixWord ++ tailWord_5977682) baseStart_5977682 baseEnd_5977682 := by
    simpa [prefixWord, tailWord_5977682, baseEnd_5977682] using wordTrace_append hprefix tailTrace_5977682
  have hstable : (prefixWord ++ tailWord_5977682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977682).length < 2 ^ (prefixWord ++ tailWord_5977682).sum := by decide
  have hdescent : baseEnd_5977682 < baseStart_5977682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977692 : List Nat := [2, 2, 4, 1, 2, 3, 2, 7]
def baseStart_5977692 : Nat := 118140960795 + 5977692 * 2 ^ 59
def prefixEnd_5977692 : Nat := 4983230072969 + 3 ^ 40 * 5977692 * 2
def baseEnd_5977692 : Nat := 113682562982819684676263

theorem tailTrace_5977692 : CollatzResearch.WordTrace tailWord_5977692 prefixEnd_5977692 113682562982819684676263 := by
  unfold tailWord_5977692
  simp only [CollatzResearch.WordTrace]
  refine ⟨109012169329925133680015665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145349559106566844906687553 109012169329925133680015665)
  ·
    refine ⟨81759126997443850260011749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109012169329925133680015665 81759126997443850260011749)
    ·
      refine ⟨15329836312020721923752203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81759126997443850260011749 15329836312020721923752203)
      ·
        refine ⟨22994754468031082885628305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15329836312020721923752203 22994754468031082885628305)
        ·
          refine ⟨17246065851023312164221229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22994754468031082885628305 17246065851023312164221229)
          ·
            refine ⟨6467274694133742061582961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17246065851023312164221229 6467274694133742061582961)
            ·
              refine ⟨4850456020600306546187221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6467274694133742061582961 4850456020600306546187221)
              ·
                refine ⟨113682562982819684676263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4850456020600306546187221 113682562982819684676263)
                ·
                  rfl

theorem cell23_5977692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 7].length) (baseStart_5977692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977692 prefixEnd_5977692 := by exact prefixLift 5977692
  have htrace : WordTrace (prefixWord ++ tailWord_5977692) baseStart_5977692 baseEnd_5977692 := by
    simpa [prefixWord, tailWord_5977692, baseEnd_5977692] using wordTrace_append hprefix tailTrace_5977692
  have hstable : (prefixWord ++ tailWord_5977692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977692).length < 2 ^ (prefixWord ++ tailWord_5977692).sum := by decide
  have hdescent : baseEnd_5977692 < baseStart_5977692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977708 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 4]
def baseStart_5977708 : Nat := 118140960795 + 5977708 * 2 ^ 59
def prefixEnd_5977708 : Nat := 4983230072969 + 3 ^ 40 * 5977708 * 2
def baseEnd_5977708 : Nat := 3069437416226603423659027

theorem tailTrace_5977708 : CollatzResearch.WordTrace tailWord_5977708 prefixEnd_5977708 3069437416226603423659027 := by
  unfold tailWord_5977708
  simp only [CollatzResearch.WordTrace]
  refine ⟨109012461113896151046306889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145349948151861534728409185 109012461113896151046306889)
  ·
    refine ⟨81759345835422113284730167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109012461113896151046306889 81759345835422113284730167)
    ·
      refine ⟨122639018753133169927095251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81759345835422113284730167 122639018753133169927095251)
      ·
        refine ⟨183958528129699754890642877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122639018753133169927095251 183958528129699754890642877)
        ·
          refine ⟨68984448048637408083991079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183958528129699754890642877 68984448048637408083991079)
          ·
            refine ⟨103476672072956112125986619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68984448048637408083991079 103476672072956112125986619)
            ·
              refine ⟨155215008109434168188979929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103476672072956112125986619 155215008109434168188979929)
              ·
                refine ⟨116411256082075626141734947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155215008109434168188979929 116411256082075626141734947)
                ·
                  refine ⟨174616884123113439212602421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116411256082075626141734947 174616884123113439212602421)
                  ·
                    refine ⟨16370332886541884926181477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 174616884123113439212602421 16370332886541884926181477)
                    ·
                      refine ⟨3069437416226603423659027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16370332886541884926181477 3069437416226603423659027)
                      ·
                        rfl

theorem cell23_5977708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_5977708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977708 prefixEnd_5977708 := by exact prefixLift 5977708
  have htrace : WordTrace (prefixWord ++ tailWord_5977708) baseStart_5977708 baseEnd_5977708 := by
    simpa [prefixWord, tailWord_5977708, baseEnd_5977708] using wordTrace_append hprefix tailTrace_5977708
  have hstable : (prefixWord ++ tailWord_5977708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977708).length < 2 ^ (prefixWord ++ tailWord_5977708).sum := by decide
  have hdescent : baseEnd_5977708 < baseStart_5977708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977728 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 5]
def baseStart_5977728 : Nat := 118140960795 + 5977728 * 2 ^ 59
def prefixEnd_5977728 : Nat := 4983230072969 + 3 ^ 40 * 5977728 * 2
def baseEnd_5977728 : Nat := 3069447685839693345408935

theorem tailTrace_5977728 : CollatzResearch.WordTrace tailWord_5977728 prefixEnd_5977728 3069447685839693345408935 := by
  unfold tailWord_5977728
  simp only [CollatzResearch.WordTrace]
  refine ⟨109012825843859922754170919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145350434458479897005561225 109012825843859922754170919)
  ·
    refine ⟨163519238765789884131256379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109012825843859922754170919 163519238765789884131256379)
    ·
      refine ⟨245278858148684826196884569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163519238765789884131256379 245278858148684826196884569)
      ·
        refine ⟨183959143611513619647663427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245278858148684826196884569 183959143611513619647663427)
        ·
          refine ⟨275938715417270429471495141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183959143611513619647663427 275938715417270429471495141)
          ·
            refine ⟨51738509140738205525905339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 275938715417270429471495141 51738509140738205525905339)
            ·
              refine ⟨77607763711107308288858009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51738509140738205525905339 77607763711107308288858009)
              ·
                refine ⟨58205822783330481216643507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77607763711107308288858009 58205822783330481216643507)
                ·
                  refine ⟨87308734174995721824965261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58205822783330481216643507 87308734174995721824965261)
                  ·
                    refine ⟨32740775315623395684361973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87308734174995721824965261 32740775315623395684361973)
                    ·
                      refine ⟨3069447685839693345408935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32740775315623395684361973 3069447685839693345408935)
                      ·
                        rfl

theorem cell23_5977728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_5977728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977728 prefixEnd_5977728 := by exact prefixLift 5977728
  have htrace : WordTrace (prefixWord ++ tailWord_5977728) baseStart_5977728 baseEnd_5977728 := by
    simpa [prefixWord, tailWord_5977728, baseEnd_5977728] using wordTrace_append hprefix tailTrace_5977728
  have hstable : (prefixWord ++ tailWord_5977728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977728).length < 2 ^ (prefixWord ++ tailWord_5977728).sum := by decide
  have hdescent : baseEnd_5977728 < baseStart_5977728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977736 : List Nat := [2, 1, 3, 5, 1, 1, 1, 3, 2, 1, 3]
def baseStart_5977736 : Nat := 118140960795 + 5977736 * 2 ^ 59
def prefixEnd_5977736 : Nat := 4983230072969 + 3 ^ 40 * 5977736 * 2
def baseEnd_5977736 : Nat := 3069451793684929314108899

theorem tailTrace_5977736 : CollatzResearch.WordTrace tailWord_5977736 prefixEnd_5977736 3069451793684929314108899 := by
  unfold tailWord_5977736
  simp only [CollatzResearch.WordTrace]
  refine ⟨109012971735845431437316531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145350628981127241916422041 109012971735845431437316531)
  ·
    refine ⟨163519457603768147155974797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109012971735845431437316531 163519457603768147155974797)
    ·
      refine ⟨61319796601413055183490549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163519457603768147155974797 61319796601413055183490549)
      ·
        refine ⟨5748730931382473923452239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61319796601413055183490549 5748730931382473923452239)
        ·
          refine ⟨8623096397073710885178359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5748730931382473923452239 8623096397073710885178359)
          ·
            refine ⟨12934644595610566327767539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8623096397073710885178359 12934644595610566327767539)
            ·
              refine ⟨19401966893415849491651309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12934644595610566327767539 19401966893415849491651309)
              ·
                refine ⟨7275737585030943559369241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19401966893415849491651309 7275737585030943559369241)
                ·
                  refine ⟨5456803188773207669526931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7275737585030943559369241 5456803188773207669526931)
                  ·
                    refine ⟨8185204783159811504290397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5456803188773207669526931 8185204783159811504290397)
                    ·
                      refine ⟨3069451793684929314108899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8185204783159811504290397 3069451793684929314108899)
                      ·
                        rfl

theorem cell23_5977736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_5977736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977736 prefixEnd_5977736 := by exact prefixLift 5977736
  have htrace : WordTrace (prefixWord ++ tailWord_5977736) baseStart_5977736 baseEnd_5977736 := by
    simpa [prefixWord, tailWord_5977736, baseEnd_5977736] using wordTrace_append hprefix tailTrace_5977736
  have hstable : (prefixWord ++ tailWord_5977736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977736).length < 2 ^ (prefixWord ++ tailWord_5977736).sum := by decide
  have hdescent : baseEnd_5977736 < baseStart_5977736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977775 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 3]
def baseStart_5977775 : Nat := 118140960795 + 5977775 * 2 ^ 59
def prefixEnd_5977775 : Nat := 4983230072969 + 3 ^ 40 * 5977775 * 2
def baseEnd_5977775 : Nat := 3069471819430454661521219

theorem tailTrace_5977775 : CollatzResearch.WordTrace tailWord_5977775 prefixEnd_5977775 3069471819430454661521219 := by
  unfold tailWord_5977775
  simp only [CollatzResearch.WordTrace]
  refine ⟨218027365918549572535302779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145351577279033048356868519 218027365918549572535302779)
  ·
    refine ⟨327041048877824358802954169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218027365918549572535302779 327041048877824358802954169)
    ·
      refine ⟨245280786658368269102215627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327041048877824358802954169 245280786658368269102215627)
      ·
        refine ⟨367921179987552403653323441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245280786658368269102215627 367921179987552403653323441)
        ·
          refine ⟨275940884990664302739992581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367921179987552403653323441 275940884990664302739992581)
          ·
            refine ⟨51738915935749556763748609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 275940884990664302739992581 51738915935749556763748609)
            ·
              refine ⟨38804186951812167572811457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51738915935749556763748609 38804186951812167572811457)
              ·
                refine ⟨29103140213859125679608593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38804186951812167572811457 29103140213859125679608593)
                ·
                  refine ⟨21827355160394344259706445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29103140213859125679608593 21827355160394344259706445)
                  ·
                    refine ⟨8185258185147879097389917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21827355160394344259706445 8185258185147879097389917)
                    ·
                      refine ⟨3069471819430454661521219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8185258185147879097389917 3069471819430454661521219)
                      ·
                        rfl

theorem cell23_5977775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 3].length) (baseStart_5977775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977775 prefixEnd_5977775 := by exact prefixLift 5977775
  have htrace : WordTrace (prefixWord ++ tailWord_5977775) baseStart_5977775 baseEnd_5977775 := by
    simpa [prefixWord, tailWord_5977775, baseEnd_5977775] using wordTrace_append hprefix tailTrace_5977775
  have hstable : (prefixWord ++ tailWord_5977775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977775).length < 2 ^ (prefixWord ++ tailWord_5977775).sum := by decide
  have hdescent : baseEnd_5977775 < baseStart_5977775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977808 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 1, 10]
def baseStart_5977808 : Nat := 118140960795 + 5977808 * 2 ^ 59
def prefixEnd_5977808 : Nat := 4983230072969 + 3 ^ 40 * 5977808 * 2
def baseEnd_5977808 : Nat := 1023162921430684344136189

theorem tailTrace_5977808 : CollatzResearch.WordTrace tailWord_5977808 prefixEnd_5977808 1023162921430684344136189 := by
  unfold tailWord_5977808
  simp only [CollatzResearch.WordTrace]
  refine ⟨109014284763715009585627039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145352379684953346114169385 109014284763715009585627039)
  ·
    refine ⟨163521427145572514378440559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109014284763715009585627039 163521427145572514378440559)
    ·
      refine ⟨245282140718358771567660839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163521427145572514378440559 245282140718358771567660839)
      ·
        refine ⟨367923211077538157351491259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245282140718358771567660839 367923211077538157351491259)
        ·
          refine ⟨551884816616307236027236889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367923211077538157351491259 551884816616307236027236889)
          ·
            refine ⟨413913612462230427020427667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551884816616307236027236889 413913612462230427020427667)
            ·
              refine ⟨620870418693345640530641501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413913612462230427020427667 620870418693345640530641501)
              ·
                refine ⟨232826407010004615198990563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 620870418693345640530641501 232826407010004615198990563)
                ·
                  refine ⟨349239610515006922798485845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232826407010004615198990563 349239610515006922798485845)
                  ·
                    refine ⟨1023162921430684344136189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 349239610515006922798485845 1023162921430684344136189)
                    ·
                      rfl

theorem cell23_5977808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 10].length) (baseStart_5977808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977808 prefixEnd_5977808 := by exact prefixLift 5977808
  have htrace : WordTrace (prefixWord ++ tailWord_5977808) baseStart_5977808 baseEnd_5977808 := by
    simpa [prefixWord, tailWord_5977808, baseEnd_5977808] using wordTrace_append hprefix tailTrace_5977808
  have hstable : (prefixWord ++ tailWord_5977808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977808).length < 2 ^ (prefixWord ++ tailWord_5977808).sum := by decide
  have hdescent : baseEnd_5977808 < baseStart_5977808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977812 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_5977812 : Nat := 118140960795 + 5977812 * 2 ^ 59
def prefixEnd_5977812 : Nat := 4983230072969 + 3 ^ 40 * 5977812 * 2
def baseEnd_5977812 : Nat := 1023163606071557005586183

theorem tailTrace_5977812 : CollatzResearch.WordTrace tailWord_5977812 prefixEnd_5977812 1023163606071557005586183 := by
  unfold tailWord_5977812
  simp only [CollatzResearch.WordTrace]
  refine ⟨109014357709707763927199845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145352476946277018569599793 109014357709707763927199845)
  ·
    refine ⟨20440192070570205736349971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109014357709707763927199845 20440192070570205736349971)
    ·
      refine ⟨30660288105855308604524957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20440192070570205736349971 30660288105855308604524957)
      ·
        refine ⟨11497608039695740726696859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30660288105855308604524957 11497608039695740726696859)
        ·
          refine ⟨17246412059543611090045289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11497608039695740726696859 17246412059543611090045289)
          ·
            refine ⟨12934809044657708317533967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17246412059543611090045289 12934809044657708317533967)
            ·
              refine ⟨19402213566986562476300951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12934809044657708317533967 19402213566986562476300951)
              ·
                refine ⟨29103320350479843714451427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19402213566986562476300951 29103320350479843714451427)
                ·
                  refine ⟨43654980525719765571677141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29103320350479843714451427 43654980525719765571677141)
                  ·
                    refine ⟨1023163606071557005586183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43654980525719765571677141 1023163606071557005586183)
                    ·
                      rfl

theorem cell23_5977812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_5977812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977812 prefixEnd_5977812 := by exact prefixLift 5977812
  have htrace : WordTrace (prefixWord ++ tailWord_5977812) baseStart_5977812 baseEnd_5977812 := by
    simpa [prefixWord, tailWord_5977812, baseEnd_5977812] using wordTrace_append hprefix tailTrace_5977812
  have hstable : (prefixWord ++ tailWord_5977812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977812).length < 2 ^ (prefixWord ++ tailWord_5977812).sum := by decide
  have hdescent : baseEnd_5977812 < baseStart_5977812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977815 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 4]
def baseStart_5977815 : Nat := 118140960795 + 5977815 * 2 ^ 59
def prefixEnd_5977815 : Nat := 4983230072969 + 3 ^ 40 * 5977815 * 2
def baseEnd_5977815 : Nat := 3069492358656634505021035

theorem tailTrace_5977815 : CollatzResearch.WordTrace tailWord_5977815 prefixEnd_5977815 3069492358656634505021035 := by
  unfold tailWord_5977815
  simp only [CollatzResearch.WordTrace]
  refine ⟨218028824838404659366758899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145352549892269772911172599 218028824838404659366758899)
  ·
    refine ⟨327043237257606989050138349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218028824838404659366758899 327043237257606989050138349)
    ·
      refine ⟨122641213971602620893801881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327043237257606989050138349 122641213971602620893801881)
      ·
        refine ⟨91980910478701965670351411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122641213971602620893801881 91980910478701965670351411)
        ·
          refine ⟨137971365718052948505527117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91980910478701965670351411 137971365718052948505527117)
          ·
            refine ⟨51739262144269855689572669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137971365718052948505527117 51739262144269855689572669)
            ·
              refine ⟨19402223304101195883589751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51739262144269855689572669 19402223304101195883589751)
              ·
                refine ⟨29103334956151793825384627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19402223304101195883589751 29103334956151793825384627)
                ·
                  refine ⟨43655002434227690738076941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29103334956151793825384627 43655002434227690738076941)
                  ·
                    refine ⟨16370625912835384026778853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43655002434227690738076941 16370625912835384026778853)
                    ·
                      refine ⟨3069492358656634505021035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16370625912835384026778853 3069492358656634505021035)
                      ·
                        rfl

theorem cell23_5977815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_5977815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977815 prefixEnd_5977815 := by exact prefixLift 5977815
  have htrace : WordTrace (prefixWord ++ tailWord_5977815) baseStart_5977815 baseEnd_5977815 := by
    simpa [prefixWord, tailWord_5977815, baseEnd_5977815] using wordTrace_append hprefix tailTrace_5977815
  have hstable : (prefixWord ++ tailWord_5977815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977815).length < 2 ^ (prefixWord ++ tailWord_5977815).sum := by decide
  have hdescent : baseEnd_5977815 < baseStart_5977815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977855 : List Nat := [1, 1, 2, 2, 1, 3, 2, 5, 6]
def baseStart_5977855 : Nat := 118140960795 + 5977855 * 2 ^ 59
def prefixEnd_5977855 : Nat := 4983230072969 + 3 ^ 40 * 5977855 * 2
def baseEnd_5977855 : Nat := 341056988653646038724539

theorem tailTrace_5977855 : CollatzResearch.WordTrace tailWord_5977855 prefixEnd_5977855 341056988653646038724539 := by
  unfold tailWord_5977855
  simp only [CollatzResearch.WordTrace]
  refine ⟨218030283758259746198215019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145353522505506497465476679 218030283758259746198215019)
  ·
    refine ⟨327045425637389619297322529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218030283758259746198215019 327045425637389619297322529)
    ·
      refine ⟨245284069228042214472991897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327045425637389619297322529 245284069228042214472991897)
      ·
        refine ⟨183963051921031660854743923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245284069228042214472991897 183963051921031660854743923)
        ·
          refine ⟨275944577881547491282115885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183963051921031660854743923 275944577881547491282115885)
          ·
            refine ⟨103479216705580309230793457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275944577881547491282115885 103479216705580309230793457)
            ·
              refine ⟨77609412529185231923095093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103479216705580309230793457 77609412529185231923095093)
              ·
                refine ⟨7275882424611115492790165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77609412529185231923095093 7275882424611115492790165)
                ·
                  refine ⟨341056988653646038724539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7275882424611115492790165 341056988653646038724539)
                  ·
                    rfl

theorem cell23_5977855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 6].length) (baseStart_5977855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977855 prefixEnd_5977855 := by exact prefixLift 5977855
  have htrace : WordTrace (prefixWord ++ tailWord_5977855) baseStart_5977855 baseEnd_5977855 := by
    simpa [prefixWord, tailWord_5977855, baseEnd_5977855] using wordTrace_append hprefix tailTrace_5977855
  have hstable : (prefixWord ++ tailWord_5977855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977855).length < 2 ^ (prefixWord ++ tailWord_5977855).sum := by decide
  have hdescent : baseEnd_5977855 < baseStart_5977855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977865 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 1, 7, 3]
def baseStart_5977865 : Nat := 118140960795 + 5977865 * 2 ^ 59
def prefixEnd_5977865 : Nat := 4983230072969 + 3 ^ 40 * 5977865 * 2
def baseEnd_5977865 : Nat := 3069518032689359309395805

theorem tailTrace_5977865 : CollatzResearch.WordTrace tailWord_5977865 prefixEnd_5977865 3069518032689359309395805 := by
  unfold tailWord_5977865
  simp only [CollatzResearch.WordTrace]
  refine ⟨218030648488223517906079049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145353765658815678604052699 218030648488223517906079049)
  ·
    refine ⟨163522986366167638429559287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218030648488223517906079049 163522986366167638429559287)
    ·
      refine ⟨245284479549251457644338931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163522986366167638429559287 245284479549251457644338931)
      ·
        refine ⟨367926719323877186466508397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245284479549251457644338931 367926719323877186466508397)
        ·
          refine ⟨137972519746453944924940649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367926719323877186466508397 137972519746453944924940649)
          ·
            refine ⟨103479389809840458693705487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137972519746453944924940649 103479389809840458693705487)
            ·
              refine ⟨155219084714760688040558231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103479389809840458693705487 155219084714760688040558231)
              ·
                refine ⟨232828627072141032060837347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155219084714760688040558231 232828627072141032060837347)
                ·
                  refine ⟨349242940608211548091256021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232828627072141032060837347 349242940608211548091256021)
                  ·
                    refine ⟨8185381420504958158388813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 349242940608211548091256021 8185381420504958158388813)
                    ·
                      refine ⟨3069518032689359309395805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8185381420504958158388813 3069518032689359309395805)
                      ·
                        rfl

theorem cell23_5977865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 7, 3].length) (baseStart_5977865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977865 prefixEnd_5977865 := by exact prefixLift 5977865
  have htrace : WordTrace (prefixWord ++ tailWord_5977865) baseStart_5977865 baseEnd_5977865 := by
    simpa [prefixWord, tailWord_5977865, baseEnd_5977865] using wordTrace_append hprefix tailTrace_5977865
  have hstable : (prefixWord ++ tailWord_5977865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977865).length < 2 ^ (prefixWord ++ tailWord_5977865).sum := by decide
  have hdescent : baseEnd_5977865 < baseStart_5977865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977966 : List Nat := [4, 1, 2, 3, 1, 1, 2, 3, 2, 4]
def baseStart_5977966 : Nat := 118140960795 + 5977966 * 2 ^ 59
def prefixEnd_5977966 : Nat := 4983230072969 + 3 ^ 40 * 5977966 * 2
def baseEnd_5977966 : Nat := 1023189964745154471410947

theorem tailTrace_5977966 : CollatzResearch.WordTrace tailWord_5977966 prefixEnd_5977966 1023189964745154471410947 := by
  unfold tailWord_5977966
  simp only [CollatzResearch.WordTrace]
  refine ⟨27254291532607201519438219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145356221507238408103670501 27254291532607201519438219)
  ·
    refine ⟨40881437298910802279157329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27254291532607201519438219 40881437298910802279157329)
    ·
      refine ⟨30661077974183101709367997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40881437298910802279157329 30661077974183101709367997)
      ·
        refine ⟨11497904240318663141012999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30661077974183101709367997 11497904240318663141012999)
        ·
          refine ⟨17246856360477994711519499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11497904240318663141012999 17246856360477994711519499)
          ·
            refine ⟨25870284540716992067279249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17246856360477994711519499 25870284540716992067279249)
            ·
              refine ⟨19402713405537744050459437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25870284540716992067279249 19402713405537744050459437)
              ·
                refine ⟨7276017527076654018922289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19402713405537744050459437 7276017527076654018922289)
                ·
                  refine ⟨5457013145307490514191717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7276017527076654018922289 5457013145307490514191717)
                  ·
                    refine ⟨1023189964745154471410947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5457013145307490514191717 1023189964745154471410947)
                    ·
                      rfl

theorem cell23_5977966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_5977966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977966 prefixEnd_5977966 := by exact prefixLift 5977966
  have htrace : WordTrace (prefixWord ++ tailWord_5977966) baseStart_5977966 baseEnd_5977966 := by
    simpa [prefixWord, tailWord_5977966, baseEnd_5977966] using wordTrace_append hprefix tailTrace_5977966
  have hstable : (prefixWord ++ tailWord_5977966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977966).length < 2 ^ (prefixWord ++ tailWord_5977966).sum := by decide
  have hdescent : baseEnd_5977966 < baseStart_5977966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5977989 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 4, 1, 3]
def baseStart_5977989 : Nat := 118140960795 + 5977989 * 2 ^ 59
def prefixEnd_5977989 : Nat := 4983230072969 + 3 ^ 40 * 5977989 * 2
def baseEnd_5977989 : Nat := 3069581704290516824245235

theorem tailTrace_5977989 : CollatzResearch.WordTrace tailWord_5977989 prefixEnd_5977989 3069581704290516824245235 := by
  unfold tailWord_5977989
  simp only [CollatzResearch.WordTrace]
  refine ⟨218035171139774287083593021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145356780759849524722395347 218035171139774287083593021)
  ·
    refine ⟨81763189177415357656347383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218035171139774287083593021 81763189177415357656347383)
    ·
      refine ⟨122644783766123036484521075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81763189177415357656347383 122644783766123036484521075)
      ·
        refine ⟨183967175649184554726781613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122644783766123036484521075 183967175649184554726781613)
        ·
          refine ⟨68987690868444208022543105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183967175649184554726781613 68987690868444208022543105)
          ·
            refine ⟨51740768151333156016907329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68987690868444208022543105 51740768151333156016907329)
            ·
              refine ⟨38805576113499867012680497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51740768151333156016907329 38805576113499867012680497)
              ·
                refine ⟨29104182085124900259510373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38805576113499867012680497 29104182085124900259510373)
                ·
                  refine ⟨5457034140960918798658195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29104182085124900259510373 5457034140960918798658195)
                  ·
                    refine ⟨8185551211441378197987293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5457034140960918798658195 8185551211441378197987293)
                    ·
                      refine ⟨3069581704290516824245235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8185551211441378197987293 3069581704290516824245235)
                      ·
                        rfl

theorem cell23_5977989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 1, 3].length) (baseStart_5977989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5977989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5977989 prefixEnd_5977989 := by exact prefixLift 5977989
  have htrace : WordTrace (prefixWord ++ tailWord_5977989) baseStart_5977989 baseEnd_5977989 := by
    simpa [prefixWord, tailWord_5977989, baseEnd_5977989] using wordTrace_append hprefix tailTrace_5977989
  have hstable : (prefixWord ++ tailWord_5977989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5977989).length < 2 ^ (prefixWord ++ tailWord_5977989).sum := by decide
  have hdescent : baseEnd_5977989 < baseStart_5977989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5977989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978030 : List Nat := [4, 1, 5, 1, 1, 2, 2, 7]
def baseStart_5978030 : Nat := 118140960795 + 5978030 * 2 ^ 59
def prefixEnd_5978030 : Nat := 4983230072969 + 3 ^ 40 * 5978030 * 2
def baseEnd_5978030 : Nat := 113688990999901894956761

theorem tailTrace_5978030 : CollatzResearch.WordTrace tailWord_5978030 prefixEnd_5978030 113688990999901894956761 := by
  unfold tailWord_5978030
  simp only [CollatzResearch.WordTrace]
  refine ⟨27254583316578218885729443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145357777688417167390557029 27254583316578218885729443)
  ·
    refine ⟨40881874974867328328594165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27254583316578218885729443 40881874974867328328594165)
    ·
      refine ⟨3832675778893812030805703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40881874974867328328594165 3832675778893812030805703)
      ·
        refine ⟨5749013668340718046208555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3832675778893812030805703 5749013668340718046208555)
        ·
          refine ⟨8623520502511077069312833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5749013668340718046208555 8623520502511077069312833)
          ·
            refine ⟨6467640376883307801984625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8623520502511077069312833 6467640376883307801984625)
            ·
              refine ⟨4850730282662480851488469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6467640376883307801984625 4850730282662480851488469)
              ·
                refine ⟨113688990999901894956761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4850730282662480851488469 113688990999901894956761)
                ·
                  rfl

theorem cell23_5978030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 7].length) (baseStart_5978030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978030 prefixEnd_5978030 := by exact prefixLift 5978030
  have htrace : WordTrace (prefixWord ++ tailWord_5978030) baseStart_5978030 baseEnd_5978030 := by
    simpa [prefixWord, tailWord_5978030, baseEnd_5978030] using wordTrace_append hprefix tailTrace_5978030
  have hstable : (prefixWord ++ tailWord_5978030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978030).length < 2 ^ (prefixWord ++ tailWord_5978030).sum := by decide
  have hdescent : baseEnd_5978030 < baseStart_5978030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978033 : List Nat := [1, 2, 2, 4, 2, 2, 2, 2, 1, 3, 2]
def baseStart_5978033 : Nat := 118140960795 + 5978033 * 2 ^ 59
def prefixEnd_5978033 : Nat := 4983230072969 + 3 ^ 40 * 5978033 * 2
def baseEnd_5978033 : Nat := 3069604297439314652095033

theorem tailTrace_5978033 : CollatzResearch.WordTrace tailWord_5978033 prefixEnd_5978033 3069604297439314652095033 := by
  unfold tailWord_5978033
  simp only [CollatzResearch.WordTrace]
  refine ⟨218036775951614882598194753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145357850634409921732129835 218036775951614882598194753)
  ·
    refine ⟨163527581963711161948646065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218036775951614882598194753 163527581963711161948646065)
    ·
      refine ⟨122645686472783371461484549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163527581963711161948646065 122645686472783371461484549)
      ·
        refine ⟨22996066213646882149028353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122645686472783371461484549 22996066213646882149028353)
        ·
          refine ⟨17247049660235161611771265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22996066213646882149028353 17247049660235161611771265)
          ·
            refine ⟨12935287245176371208828449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17247049660235161611771265 12935287245176371208828449)
            ·
              refine ⟨9701465433882278406621337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12935287245176371208828449 9701465433882278406621337)
              ·
                refine ⟨7276099075411708804966003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9701465433882278406621337 7276099075411708804966003)
                ·
                  refine ⟨10914148613117563207449005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7276099075411708804966003 10914148613117563207449005)
                  ·
                    refine ⟨4092805729919086202793377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10914148613117563207449005 4092805729919086202793377)
                    ·
                      refine ⟨3069604297439314652095033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4092805729919086202793377 3069604297439314652095033)
                      ·
                        rfl

theorem cell23_5978033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_5978033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978033 prefixEnd_5978033 := by exact prefixLift 5978033
  have htrace : WordTrace (prefixWord ++ tailWord_5978033) baseStart_5978033 baseEnd_5978033 := by
    simpa [prefixWord, tailWord_5978033, baseEnd_5978033] using wordTrace_append hprefix tailTrace_5978033
  have hstable : (prefixWord ++ tailWord_5978033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978033).length < 2 ^ (prefixWord ++ tailWord_5978033).sum := by decide
  have hdescent : baseEnd_5978033 < baseStart_5978033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978042 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4]
def baseStart_5978042 : Nat := 118140960795 + 5978042 * 2 ^ 59
def prefixEnd_5978042 : Nat := 4983230072969 + 3 ^ 40 * 5978042 * 2
def baseEnd_5978042 : Nat := 3069608918765205116882491

theorem tailTrace_5978042 : CollatzResearch.WordTrace tailWord_5978042 prefixEnd_5978042 3069608918765205116882491 := by
  unfold tailWord_5978042
  simp only [CollatzResearch.WordTrace]
  refine ⟨54509276052145569283818095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145358069472388184756848253 54509276052145569283818095)
  ·
    refine ⟨81763914078218353925727143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54509276052145569283818095 81763914078218353925727143)
    ·
      refine ⟨122645871117327530888590715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81763914078218353925727143 122645871117327530888590715)
      ·
        refine ⟨183968806675991296332886073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122645871117327530888590715 183968806675991296332886073)
        ·
          refine ⟨137976605006993472249664555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183968806675991296332886073 137976605006993472249664555)
          ·
            refine ⟨206964907510490208374496833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137976605006993472249664555 206964907510490208374496833)
            ·
              refine ⟨155223680632867656280872625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206964907510490208374496833 155223680632867656280872625)
              ·
                refine ⟨116417760474650742210654469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155223680632867656280872625 116417760474650742210654469)
                ·
                  refine ⟨21828330088997014164497713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116417760474650742210654469 21828330088997014164497713)
                  ·
                    refine ⟨16371247566747760623373285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21828330088997014164497713 16371247566747760623373285)
                    ·
                      refine ⟨3069608918765205116882491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16371247566747760623373285 3069608918765205116882491)
                      ·
                        rfl

theorem cell23_5978042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_5978042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978042 prefixEnd_5978042 := by exact prefixLift 5978042
  have htrace : WordTrace (prefixWord ++ tailWord_5978042) baseStart_5978042 baseEnd_5978042 := by
    simpa [prefixWord, tailWord_5978042, baseEnd_5978042] using wordTrace_append hprefix tailTrace_5978042
  have hstable : (prefixWord ++ tailWord_5978042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978042).length < 2 ^ (prefixWord ++ tailWord_5978042).sum := by decide
  have hdescent : baseEnd_5978042 < baseStart_5978042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978062 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_5978062 : Nat := 118140960795 + 5978062 * 2 ^ 59
def prefixEnd_5978062 : Nat := 4983230072969 + 3 ^ 40 * 5978062 * 2
def baseEnd_5978062 : Nat := 3069619188378295038632399

theorem tailTrace_5978062 : CollatzResearch.WordTrace tailWord_5978062 prefixEnd_5978062 3069619188378295038632399 := by
  unfold tailWord_5978062
  simp only [CollatzResearch.WordTrace]
  refine ⟨27254729208563727568875055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145358555779006547034000293 27254729208563727568875055)
  ·
    refine ⟨40882093812845591353312583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27254729208563727568875055 40882093812845591353312583)
    ·
      refine ⟨61323140719268387029968875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40882093812845591353312583 61323140719268387029968875)
      ·
        refine ⟨91984711078902580544953313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61323140719268387029968875 91984711078902580544953313)
        ·
          refine ⟨68988533309176935408714985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91984711078902580544953313 68988533309176935408714985)
          ·
            refine ⟨51741399981882701556536239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68988533309176935408714985 51741399981882701556536239)
            ·
              refine ⟨77612099972824052334804359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51741399981882701556536239 77612099972824052334804359)
              ·
                refine ⟨116418149959236078502206539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77612099972824052334804359 116418149959236078502206539)
                ·
                  refine ⟨174627224938854117753309809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116418149959236078502206539 174627224938854117753309809)
                  ·
                    refine ⟨130970418704140588314982357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 174627224938854117753309809 130970418704140588314982357)
                    ·
                      refine ⟨3069619188378295038632399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130970418704140588314982357 3069619188378295038632399)
                      ·
                        rfl

theorem cell23_5978062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_5978062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978062 prefixEnd_5978062 := by exact prefixLift 5978062
  have htrace : WordTrace (prefixWord ++ tailWord_5978062) baseStart_5978062 baseEnd_5978062 := by
    simpa [prefixWord, tailWord_5978062, baseEnd_5978062] using wordTrace_append hprefix tailTrace_5978062
  have hstable : (prefixWord ++ tailWord_5978062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978062).length < 2 ^ (prefixWord ++ tailWord_5978062).sum := by decide
  have hdescent : baseEnd_5978062 < baseStart_5978062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978069 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 7]
def baseStart_5978069 : Nat := 118140960795 + 5978069 * 2 ^ 59
def prefixEnd_5978069 : Nat := 4983230072969 + 3 ^ 40 * 5978069 * 2
def baseEnd_5978069 : Nat := 341069198082541834582763

theorem tailTrace_5978069 : CollatzResearch.WordTrace tailWord_5978069 prefixEnd_5978069 341069198082541834582763 := by
  unfold tailWord_5978069
  simp only [CollatzResearch.WordTrace]
  refine ⟨218038088979484460746505261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145358725986322973831003507 218038088979484460746505261)
  ·
    refine ⟨81764283367306672779939473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218038088979484460746505261 81764283367306672779939473)
    ·
      refine ⟨61323212525480004584954605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81764283367306672779939473 61323212525480004584954605)
      ·
        refine ⟨22996204697055001719357977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61323212525480004584954605 22996204697055001719357977)
        ·
          refine ⟨17247153522791251289518483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22996204697055001719357977 17247153522791251289518483)
          ·
            refine ⟨25870730284186876934277725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17247153522791251289518483 25870730284186876934277725)
            ·
              refine ⟨9701523856570078850354147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25870730284186876934277725 9701523856570078850354147)
              ·
                refine ⟨14552285784855118275531221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9701523856570078850354147 14552285784855118275531221)
                ·
                  refine ⟨341069198082541834582763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14552285784855118275531221 341069198082541834582763)
                  ·
                    rfl

theorem cell23_5978069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 7].length) (baseStart_5978069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978069 prefixEnd_5978069 := by exact prefixLift 5978069
  have htrace : WordTrace (prefixWord ++ tailWord_5978069) baseStart_5978069 baseEnd_5978069 := by
    simpa [prefixWord, tailWord_5978069, baseEnd_5978069] using wordTrace_append hprefix tailTrace_5978069
  have hstable : (prefixWord ++ tailWord_5978069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978069).length < 2 ^ (prefixWord ++ tailWord_5978069).sum := by decide
  have hdescent : baseEnd_5978069 < baseStart_5978069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978136 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 2, 4, 2]
def baseStart_5978136 : Nat := 118140960795 + 5978136 * 2 ^ 59
def prefixEnd_5978136 : Nat := 4983230072969 + 3 ^ 40 * 5978136 * 2
def baseEnd_5978136 : Nat := 3069657185946727749107059

theorem tailTrace_5978136 : CollatzResearch.WordTrace tailWord_5978136 prefixEnd_5978136 3069657185946727749107059 := by
  unfold tailWord_5978136
  simp only [CollatzResearch.WordTrace]
  refine ⟨109020266335120865594597131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145360355113494487459462841 109020266335120865594597131)
  ·
    refine ⟨163530399502681298391895697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109020266335120865594597131 163530399502681298391895697)
    ·
      refine ⟨122647799627010973793921773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163530399502681298391895697 122647799627010973793921773)
      ·
        refine ⟨45992924860129115172720665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122647799627010973793921773 45992924860129115172720665)
        ·
          refine ⟨34494693645096836379540499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45992924860129115172720665 34494693645096836379540499)
          ·
            refine ⟨51742040467645254569310749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34494693645096836379540499 51742040467645254569310749)
            ·
              refine ⟨19403265175366970463491531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51742040467645254569310749 19403265175366970463491531)
              ·
                refine ⟨29104897763050455695237297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19403265175366970463491531 29104897763050455695237297)
                ·
                  refine ⟨21828673322287841771427973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29104897763050455695237297 21828673322287841771427973)
                  ·
                    refine ⟨4092876247928970332142745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21828673322287841771427973 4092876247928970332142745)
                    ·
                      refine ⟨3069657185946727749107059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4092876247928970332142745 3069657185946727749107059)
                      ·
                        rfl

theorem cell23_5978136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_5978136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978136 prefixEnd_5978136 := by exact prefixLift 5978136
  have htrace : WordTrace (prefixWord ++ tailWord_5978136) baseStart_5978136 baseEnd_5978136 := by
    simpa [prefixWord, tailWord_5978136, baseEnd_5978136] using wordTrace_append hprefix tailTrace_5978136
  have hstable : (prefixWord ++ tailWord_5978136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978136).length < 2 ^ (prefixWord ++ tailWord_5978136).sum := by decide
  have hdescent : baseEnd_5978136 < baseStart_5978136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978146 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_5978146 : Nat := 118140960795 + 5978146 * 2 ^ 59
def prefixEnd_5978146 : Nat := 4983230072969 + 3 ^ 40 * 5978146 * 2
def baseEnd_5978146 : Nat := 1023220773584424236660671

theorem tailTrace_5978146 : CollatzResearch.WordTrace tailWord_5978146 prefixEnd_5978146 1023220773584424236660671 := by
  unfold tailWord_5978146
  simp only [CollatzResearch.WordTrace]
  refine ⟨54510224350051375724264573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145360598266803668598038861 54510224350051375724264573)
  ·
    refine ⟨20441334131269265896599215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54510224350051375724264573 20441334131269265896599215)
    ·
      refine ⟨30662001196903898844898823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20441334131269265896599215 30662001196903898844898823)
      ·
        refine ⟨45993001795355848267348235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30662001196903898844898823 45993001795355848267348235)
        ·
          refine ⟨68989502693033772401022353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45993001795355848267348235 68989502693033772401022353)
          ·
            refine ⟨51742127019775329300766765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68989502693033772401022353 51742127019775329300766765)
            ·
              refine ⟨19403297632415748487787537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51742127019775329300766765 19403297632415748487787537)
              ·
                refine ⟨14552473224311811365840653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19403297632415748487787537 14552473224311811365840653)
                ·
                  refine ⟨5457177459116929262190245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14552473224311811365840653 5457177459116929262190245)
                  ·
                    refine ⟨1023220773584424236660671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5457177459116929262190245 1023220773584424236660671)
                    ·
                      rfl

theorem cell23_5978146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_5978146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978146 prefixEnd_5978146 := by exact prefixLift 5978146
  have htrace : WordTrace (prefixWord ++ tailWord_5978146) baseStart_5978146 baseEnd_5978146 := by
    simpa [prefixWord, tailWord_5978146, baseEnd_5978146] using wordTrace_append hprefix tailTrace_5978146
  have hstable : (prefixWord ++ tailWord_5978146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978146).length < 2 ^ (prefixWord ++ tailWord_5978146).sum := by decide
  have hdescent : baseEnd_5978146 < baseStart_5978146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978176 : List Nat := [2, 1, 1, 2, 2, 6, 1, 2, 6]
def baseStart_5978176 : Nat := 118140960795 + 5978176 * 2 ^ 59
def prefixEnd_5978176 : Nat := 4983230072969 + 3 ^ 40 * 5978176 * 2
def baseEnd_5978176 : Nat := 341075302796989732511875

theorem tailTrace_5978176 : CollatzResearch.WordTrace tailWord_5978176 prefixEnd_5978176 341075302796989732511875 := by
  unfold tailWord_5978176
  simp only [CollatzResearch.WordTrace]
  refine ⟨109020995795048409010325191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145361327726731212013766921 109020995795048409010325191)
  ·
    refine ⟨163531493692572613515487787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109020995795048409010325191 163531493692572613515487787)
    ·
      refine ⟨245297240538858920273231681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163531493692572613515487787 245297240538858920273231681)
      ·
        refine ⟨183972930404144190204923761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245297240538858920273231681 183972930404144190204923761)
        ·
          refine ⟨137979697803108142653692821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183972930404144190204923761 137979697803108142653692821)
          ·
            refine ⟨6467798334520694186891851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 137979697803108142653692821 6467798334520694186891851)
            ·
              refine ⟨9701697501781041280337777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6467798334520694186891851 9701697501781041280337777)
              ·
                refine ⟨7276273126335780960253333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9701697501781041280337777 7276273126335780960253333)
                ·
                  refine ⟨341075302796989732511875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7276273126335780960253333 341075302796989732511875)
                  ·
                    rfl

theorem cell23_5978176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 6].length) (baseStart_5978176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978176 prefixEnd_5978176 := by exact prefixLift 5978176
  have htrace : WordTrace (prefixWord ++ tailWord_5978176) baseStart_5978176 baseEnd_5978176 := by
    simpa [prefixWord, tailWord_5978176, baseEnd_5978176] using wordTrace_append hprefix tailTrace_5978176
  have hstable : (prefixWord ++ tailWord_5978176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978176).length < 2 ^ (prefixWord ++ tailWord_5978176).sum := by decide
  have hdescent : baseEnd_5978176 < baseStart_5978176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978220 : List Nat := [2, 2, 1, 1, 3, 3, 3, 3, 1, 1, 3]
def baseStart_5978220 : Nat := 118140960795 + 5978220 * 2 ^ 59
def prefixEnd_5978220 : Nat := 4983230072969 + 3 ^ 40 * 5978220 * 2
def baseEnd_5978220 : Nat := 3069700318321705420456673

theorem tailTrace_5978220 : CollatzResearch.WordTrace tailWord_5978220 prefixEnd_5978220 3069700318321705420456673 := by
  unfold tailWord_5978220
  simp only [CollatzResearch.WordTrace]
  refine ⟨109021798200968706767626057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145362397601291609023501409 109021798200968706767626057)
  ·
    refine ⟨81766348650726530075719543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109021798200968706767626057 81766348650726530075719543)
    ·
      refine ⟨122649522976089795113579315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81766348650726530075719543 122649522976089795113579315)
      ·
        refine ⟨183974284464134692670368973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122649522976089795113579315 183974284464134692670368973)
        ·
          refine ⟨68990356674050509751388365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183974284464134692670368973 68990356674050509751388365)
          ·
            refine ⟨25871383752768941156770637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68990356674050509751388365 25871383752768941156770637)
            ·
              refine ⟨9701768907288352933788989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25871383752768941156770637 9701768907288352933788989)
              ·
                refine ⟨3638163340233132350170871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9701768907288352933788989 3638163340233132350170871)
                ·
                  refine ⟨5457245010349698525256307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3638163340233132350170871 5457245010349698525256307)
                  ·
                    refine ⟨8185867515524547787884461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5457245010349698525256307 8185867515524547787884461)
                    ·
                      refine ⟨3069700318321705420456673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8185867515524547787884461 3069700318321705420456673)
                      ·
                        rfl

theorem cell23_5978220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 1, 1, 3].length) (baseStart_5978220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978220 prefixEnd_5978220 := by exact prefixLift 5978220
  have htrace : WordTrace (prefixWord ++ tailWord_5978220) baseStart_5978220 baseEnd_5978220 := by
    simpa [prefixWord, tailWord_5978220, baseEnd_5978220] using wordTrace_append hprefix tailTrace_5978220
  have hstable : (prefixWord ++ tailWord_5978220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978220).length < 2 ^ (prefixWord ++ tailWord_5978220).sum := by decide
  have hdescent : baseEnd_5978220 < baseStart_5978220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978230 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2]
def baseStart_5978230 : Nat := 118140960795 + 5978230 * 2 ^ 59
def prefixEnd_5978230 : Nat := 4983230072969 + 3 ^ 40 * 5978230 * 2
def baseEnd_5978230 : Nat := 3069705453128250381331627

theorem tailTrace_5978230 : CollatzResearch.WordTrace tailWord_5978230 prefixEnd_5978230 3069705453128250381331627 := by
  unfold tailWord_5978230
  simp only [CollatzResearch.WordTrace]
  refine ⟨13627747570743824077694759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145362640754600790162077429 13627747570743824077694759)
  ·
    refine ⟨20441621356115736116542139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13627747570743824077694759 20441621356115736116542139)
    ·
      refine ⟨30662432034173604174813209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20441621356115736116542139 30662432034173604174813209)
      ·
        refine ⟨22996824025630203131109907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30662432034173604174813209 22996824025630203131109907)
        ·
          refine ⟨34495236038445304696664861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22996824025630203131109907 34495236038445304696664861)
          ·
            refine ⟨12935713514416989261249323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34495236038445304696664861 12935713514416989261249323)
            ·
              refine ⟨19403570271625483891873985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12935713514416989261249323 19403570271625483891873985)
              ·
                refine ⟨14552677703719112918905489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19403570271625483891873985 14552677703719112918905489)
                ·
                  refine ⟨10914508277789334689179117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14552677703719112918905489 10914508277789334689179117)
                  ·
                    refine ⟨4092940604171000508442169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10914508277789334689179117 4092940604171000508442169)
                    ·
                      refine ⟨3069705453128250381331627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4092940604171000508442169 3069705453128250381331627)
                      ·
                        rfl

theorem cell23_5978230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_5978230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978230 prefixEnd_5978230 := by exact prefixLift 5978230
  have htrace : WordTrace (prefixWord ++ tailWord_5978230) baseStart_5978230 baseEnd_5978230 := by
    simpa [prefixWord, tailWord_5978230, baseEnd_5978230] using wordTrace_append hprefix tailTrace_5978230
  have hstable : (prefixWord ++ tailWord_5978230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978230).length < 2 ^ (prefixWord ++ tailWord_5978230).sum := by decide
  have hdescent : baseEnd_5978230 < baseStart_5978230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978236 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 4, 4]
def baseStart_5978236 : Nat := 118140960795 + 5978236 * 2 ^ 59
def prefixEnd_5978236 : Nat := 4983230072969 + 3 ^ 40 * 5978236 * 2
def baseEnd_5978236 : Nat := 1023236178004059119285533

theorem tailTrace_5978236 : CollatzResearch.WordTrace tailWord_5978236 prefixEnd_5978236 1023236178004059119285533 := by
  unfold tailWord_5978236
  simp only [CollatzResearch.WordTrace]
  refine ⟨109022089984939724133917281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145362786646586298845223041 109022089984939724133917281)
  ·
    refine ⟨81766567488704793100437961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109022089984939724133917281 81766567488704793100437961)
    ·
      refine ⟨61324925616528594825328471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81766567488704793100437961 61324925616528594825328471)
      ·
        refine ⟨91987388424792892237992707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61324925616528594825328471 91987388424792892237992707)
        ·
          refine ⟨137981082637189338356989061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91987388424792892237992707 137981082637189338356989061)
          ·
            refine ⟨25871452994473000941935449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137981082637189338356989061 25871452994473000941935449)
            ·
              refine ⟨19403589745854750706451587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25871452994473000941935449 19403589745854750706451587)
              ·
                refine ⟨29105384618782126059677381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19403589745854750706451587 29105384618782126059677381)
                ·
                  refine ⟨5457259616021648636189509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29105384618782126059677381 5457259616021648636189509)
                  ·
                    refine ⟨1023236178004059119285533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5457259616021648636189509 1023236178004059119285533)
                    ·
                      rfl

theorem cell23_5978236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_5978236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978236 prefixEnd_5978236 := by exact prefixLift 5978236
  have htrace : WordTrace (prefixWord ++ tailWord_5978236) baseStart_5978236 baseEnd_5978236 := by
    simpa [prefixWord, tailWord_5978236, baseEnd_5978236] using wordTrace_append hprefix tailTrace_5978236
  have hstable : (prefixWord ++ tailWord_5978236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978236).length < 2 ^ (prefixWord ++ tailWord_5978236).sum := by decide
  have hdescent : baseEnd_5978236 < baseStart_5978236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978237 : List Nat := [1, 4, 1, 1, 3, 3, 3, 2, 1, 1, 3]
def baseStart_5978237 : Nat := 118140960795 + 5978237 * 2 ^ 59
def prefixEnd_5978237 : Nat := 4983230072969 + 3 ^ 40 * 5978237 * 2
def baseEnd_5978237 : Nat := 3069709047492831853944095

theorem tailTrace_5978237 : CollatzResearch.WordTrace tailWord_5978237 prefixEnd_5978237 3069709047492831853944095 := by
  unfold tailWord_5978237
  simp only [CollatzResearch.WordTrace]
  refine ⟨218044216442875825438620965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145362810961917216959080643 218044216442875825438620965)
  ·
    refine ⟨40883290583039217269741431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218044216442875825438620965 40883290583039217269741431)
    ·
      refine ⟨61324935874558825904612147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40883290583039217269741431 61324935874558825904612147)
      ·
        refine ⟨91987403811838238856918221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61324935874558825904612147 91987403811838238856918221)
        ·
          refine ⟨34495276429439339571344333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91987403811838238856918221 34495276429439339571344333)
          ·
            refine ⟨12935728661039752339254125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34495276429439339571344333 12935728661039752339254125)
            ·
              refine ⟨4850898247889907127220297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12935728661039752339254125 4850898247889907127220297)
              ·
                refine ⟨3638173685917430345415223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4850898247889907127220297 3638173685917430345415223)
                ·
                  refine ⟨5457260528876145518122835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3638173685917430345415223 5457260528876145518122835)
                  ·
                    refine ⟨8185890793314218277184253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5457260528876145518122835 8185890793314218277184253)
                    ·
                      refine ⟨3069709047492831853944095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8185890793314218277184253 3069709047492831853944095)
                      ·
                        rfl

theorem cell23_5978237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_5978237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978237 prefixEnd_5978237 := by exact prefixLift 5978237
  have htrace : WordTrace (prefixWord ++ tailWord_5978237) baseStart_5978237 baseEnd_5978237 := by
    simpa [prefixWord, tailWord_5978237, baseEnd_5978237] using wordTrace_append hprefix tailTrace_5978237
  have hstable : (prefixWord ++ tailWord_5978237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978237).length < 2 ^ (prefixWord ++ tailWord_5978237).sum := by decide
  have hdescent : baseEnd_5978237 < baseStart_5978237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978249 : List Nat := [1, 2, 1, 1, 4, 2, 4, 8]
def baseStart_5978249 : Nat := 118140960795 + 5978249 * 2 ^ 59
def prefixEnd_5978249 : Nat := 4983230072969 + 3 ^ 40 * 5978249 * 2
def baseEnd_5978249 : Nat := 113693155898543918777557

theorem tailTrace_5978249 : CollatzResearch.WordTrace tailWord_5978249 prefixEnd_5978249 113693155898543918777557 := by
  unfold tailWord_5978249
  simp only [CollatzResearch.WordTrace]
  refine ⟨218044654118832351488057801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145363102745888234325371867 218044654118832351488057801)
  ·
    refine ⟨163533490589124263616043351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218044654118832351488057801 163533490589124263616043351)
    ·
      refine ⟨245300235883686395424065027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163533490589124263616043351 245300235883686395424065027)
      ·
        refine ⟨367950353825529593136097541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245300235883686395424065027 367950353825529593136097541)
        ·
          refine ⟨68990691342286798713018289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 367950353825529593136097541 68990691342286798713018289)
          ·
            refine ⟨51743018506715099034763717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68990691342286798713018289 51743018506715099034763717)
            ·
              refine ⟨9701815970009081069018197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51743018506715099034763717 9701815970009081069018197)
              ·
                refine ⟨113693155898543918777557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9701815970009081069018197 113693155898543918777557)
                ·
                  rfl

theorem cell23_5978249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 8].length) (baseStart_5978249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978249 prefixEnd_5978249 := by exact prefixLift 5978249
  have htrace : WordTrace (prefixWord ++ tailWord_5978249) baseStart_5978249 baseEnd_5978249 := by
    simpa [prefixWord, tailWord_5978249, baseEnd_5978249] using wordTrace_append hprefix tailTrace_5978249
  have hstable : (prefixWord ++ tailWord_5978249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978249).length < 2 ^ (prefixWord ++ tailWord_5978249).sum := by decide
  have hdescent : baseEnd_5978249 < baseStart_5978249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978260 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_5978260 : Nat := 118140960795 + 5978260 * 2 ^ 59
def prefixEnd_5978260 : Nat := 4983230072969 + 3 ^ 40 * 5978260 * 2
def baseEnd_5978260 : Nat := 3069720857547885263956489

theorem tailTrace_5978260 : CollatzResearch.WordTrace tailWord_5978260 prefixEnd_5978260 3069720857547885263956489 := by
  unfold tailWord_5978260
  simp only [CollatzResearch.WordTrace]
  refine ⟨109022527660896250183354117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145363370214528333577805489 109022527660896250183354117)
  ·
    refine ⟨20441723936418046909378897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109022527660896250183354117 20441723936418046909378897)
    ·
      refine ⟨15331292952313535182034173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20441723936418046909378897 15331292952313535182034173)
      ·
        refine ⟨5749234857117575693262815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15331292952313535182034173 5749234857117575693262815)
        ·
          refine ⟨8623852285676363539894223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5749234857117575693262815 8623852285676363539894223)
          ·
            refine ⟨12935778428514545309841335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8623852285676363539894223 12935778428514545309841335)
            ·
              refine ⟨19403667642771817964762003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12935778428514545309841335 19403667642771817964762003)
              ·
                refine ⟨29105501464157726947143005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19403667642771817964762003 29105501464157726947143005)
                ·
                  refine ⟨10914563049059147605178627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29105501464157726947143005 10914563049059147605178627)
                  ·
                    refine ⟨16371844573588721407767941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10914563049059147605178627 16371844573588721407767941)
                    ·
                      refine ⟨3069720857547885263956489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16371844573588721407767941 3069720857547885263956489)
                      ·
                        rfl

theorem cell23_5978260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_5978260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978260 prefixEnd_5978260 := by exact prefixLift 5978260
  have htrace : WordTrace (prefixWord ++ tailWord_5978260) baseStart_5978260 baseEnd_5978260 := by
    simpa [prefixWord, tailWord_5978260, baseEnd_5978260] using wordTrace_append hprefix tailTrace_5978260
  have hstable : (prefixWord ++ tailWord_5978260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978260).length < 2 ^ (prefixWord ++ tailWord_5978260).sum := by decide
  have hdescent : baseEnd_5978260 < baseStart_5978260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978263 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 3]
def baseStart_5978263 : Nat := 118140960795 + 5978263 * 2 ^ 59
def prefixEnd_5978263 : Nat := 4983230072969 + 3 ^ 40 * 5978263 * 2
def baseEnd_5978263 : Nat := 3069722397989848752218975

theorem tailTrace_5978263 : CollatzResearch.WordTrace tailWord_5978263 prefixEnd_5978263 3069722397989848752218975 := by
  unfold tailWord_5978263
  simp only [CollatzResearch.WordTrace]
  refine ⟨218045164740781631879067443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145363443160521087919378295 218045164740781631879067443)
  ·
    refine ⟨327067747111172447818601165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218045164740781631879067443 327067747111172447818601165)
    ·
      refine ⟨122650405166689667931975437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327067747111172447818601165 122650405166689667931975437)
      ·
        refine ⟨45993901937508625474490789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122650405166689667931975437 45993901937508625474490789)
        ·
          refine ⟨8623856613282867276467023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45993901937508625474490789 8623856613282867276467023)
          ·
            refine ⟨12935784919924300914700535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8623856613282867276467023 12935784919924300914700535)
            ·
              refine ⟨19403677379886451372050803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12935784919924300914700535 19403677379886451372050803)
              ·
                refine ⟨29105516069829677058076205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19403677379886451372050803 29105516069829677058076205)
                ·
                  refine ⟨10914568526186128896778577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29105516069829677058076205 10914568526186128896778577)
                  ·
                    refine ⟨8185926394639596672583933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10914568526186128896778577 8185926394639596672583933)
                    ·
                      refine ⟨3069722397989848752218975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8185926394639596672583933 3069722397989848752218975)
                      ·
                        rfl

theorem cell23_5978263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_5978263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978263 prefixEnd_5978263 := by exact prefixLift 5978263
  have htrace : WordTrace (prefixWord ++ tailWord_5978263) baseStart_5978263 baseEnd_5978263 := by
    simpa [prefixWord, tailWord_5978263, baseEnd_5978263] using wordTrace_append hprefix tailTrace_5978263
  have hstable : (prefixWord ++ tailWord_5978263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978263).length < 2 ^ (prefixWord ++ tailWord_5978263).sum := by decide
  have hdescent : baseEnd_5978263 < baseStart_5978263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978299 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 4]
def baseStart_5978299 : Nat := 118140960795 + 5978299 * 2 ^ 59
def prefixEnd_5978299 : Nat := 4983230072969 + 3 ^ 40 * 5978299 * 2
def baseEnd_5978299 : Nat := 3069740883293410611368809

theorem tailTrace_5978299 : CollatzResearch.WordTrace tailWord_5978299 prefixEnd_5978299 3069740883293410611368809 := by
  unfold tailWord_5978299
  simp only [CollatzResearch.WordTrace]
  refine ⟨218046477768651210027377951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145364318512434140018251967 218046477768651210027377951)
  ·
    refine ⟨327069716652976815041066927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218046477768651210027377951 327069716652976815041066927)
    ·
      refine ⟨490604574979465222561600391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327069716652976815041066927 490604574979465222561600391)
      ·
        refine ⟨735906862469197833842400587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490604574979465222561600391 735906862469197833842400587)
        ·
          refine ⟨1103860293703796750763600881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735906862469197833842400587 1103860293703796750763600881)
          ·
            refine ⟨827895220277847563072700661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1103860293703796750763600881 827895220277847563072700661)
            ·
              refine ⟨77615176901048209038065687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 827895220277847563072700661 77615176901048209038065687)
              ·
                refine ⟨116422765351572313557098531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77615176901048209038065687 116422765351572313557098531)
                ·
                  refine ⟨174634148027358470335647797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116422765351572313557098531 174634148027358470335647797)
                  ·
                    refine ⟨16371951377564856593966981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 174634148027358470335647797 16371951377564856593966981)
                    ·
                      refine ⟨3069740883293410611368809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16371951377564856593966981 3069740883293410611368809)
                      ·
                        rfl

theorem cell23_5978299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 4].length) (baseStart_5978299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978299 prefixEnd_5978299 := by exact prefixLift 5978299
  have htrace : WordTrace (prefixWord ++ tailWord_5978299) baseStart_5978299 baseEnd_5978299 := by
    simpa [prefixWord, tailWord_5978299, baseEnd_5978299] using wordTrace_append hprefix tailTrace_5978299
  have hstable : (prefixWord ++ tailWord_5978299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978299).length < 2 ^ (prefixWord ++ tailWord_5978299).sum := by decide
  have hdescent : baseEnd_5978299 < baseStart_5978299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978309 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 1, 8]
def baseStart_5978309 : Nat := 118140960795 + 5978309 * 2 ^ 59
def prefixEnd_5978309 : Nat := 4983230072969 + 3 ^ 40 * 5978309 * 2
def baseEnd_5978309 : Nat := 1023248672699985190747921

theorem tailTrace_5978309 : CollatzResearch.WordTrace tailWord_5978309 prefixEnd_5978309 1023248672699985190747921 := by
  unfold tailWord_5978309
  simp only [CollatzResearch.WordTrace]
  refine ⟨218046842498614981735241981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145364561665743321156827987 218046842498614981735241981)
  ·
    refine ⟨81767565936980618150715743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218046842498614981735241981 81767565936980618150715743)
    ·
      refine ⟨122651348905470927226073615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81767565936980618150715743 122651348905470927226073615)
      ·
        refine ⟨183977023358206390839110423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122651348905470927226073615 183977023358206390839110423)
        ·
          refine ⟨275965535037309586258665635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183977023358206390839110423 275965535037309586258665635)
          ·
            refine ⟨413948302555964379387998453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275965535037309586258665635 413948302555964379387998453)
            ·
              refine ⟨38807653364621660567624855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 413948302555964379387998453 38807653364621660567624855)
              ·
                refine ⟨58211480046932490851437283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38807653364621660567624855 58211480046932490851437283)
                ·
                  refine ⟨87317220070398736277155925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58211480046932490851437283 87317220070398736277155925)
                  ·
                    refine ⟨1023248672699985190747921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87317220070398736277155925 1023248672699985190747921)
                    ·
                      rfl

theorem cell23_5978309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_5978309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978309 prefixEnd_5978309 := by exact prefixLift 5978309
  have htrace : WordTrace (prefixWord ++ tailWord_5978309) baseStart_5978309 baseEnd_5978309 := by
    simpa [prefixWord, tailWord_5978309, baseEnd_5978309] using wordTrace_append hprefix tailTrace_5978309
  have hstable : (prefixWord ++ tailWord_5978309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978309).length < 2 ^ (prefixWord ++ tailWord_5978309).sum := by decide
  have hdescent : baseEnd_5978309 < baseStart_5978309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978346 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_5978346 : Nat := 118140960795 + 5978346 * 2 ^ 59
def prefixEnd_5978346 : Nat := 4983230072969 + 3 ^ 40 * 5978346 * 2
def baseEnd_5978346 : Nat := 3069765016884171927481093

theorem tailTrace_5978346 : CollatzResearch.WordTrace tailWord_5978346 prefixEnd_5978346 3069765016884171927481093 := by
  unfold tailWord_5978346
  simp only [CollatzResearch.WordTrace]
  refine ⟨54512047999870234263584723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145365461332987291369559261 54512047999870234263584723)
  ·
    refine ⟨81768071999805351395377085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54512047999870234263584723 81768071999805351395377085)
    ·
      refine ⟨30663026999927006773266407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81768071999805351395377085 30663026999927006773266407)
      ·
        refine ⟨45994540499890510159899611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30663026999927006773266407 45994540499890510159899611)
        ·
          refine ⟨68991810749835765239849417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45994540499890510159899611 68991810749835765239849417)
          ·
            refine ⟨51743858062376823929887063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68991810749835765239849417 51743858062376823929887063)
            ·
              refine ⟨77615787093565235894830595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51743858062376823929887063 77615787093565235894830595)
              ·
                refine ⟨116423680640347853842245893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77615787093565235894830595 116423680640347853842245893)
                ·
                  refine ⟨21829440120065222595421105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116423680640347853842245893 21829440120065222595421105)
                  ·
                    refine ⟨16372080090048916946565829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21829440120065222595421105 16372080090048916946565829)
                    ·
                      refine ⟨3069765016884171927481093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16372080090048916946565829 3069765016884171927481093)
                      ·
                        rfl

theorem cell23_5978346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_5978346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978346 prefixEnd_5978346 := by exact prefixLift 5978346
  have htrace : WordTrace (prefixWord ++ tailWord_5978346) baseStart_5978346 baseEnd_5978346 := by
    simpa [prefixWord, tailWord_5978346, baseEnd_5978346] using wordTrace_append hprefix tailTrace_5978346
  have hstable : (prefixWord ++ tailWord_5978346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978346).length < 2 ^ (prefixWord ++ tailWord_5978346).sum := by decide
  have hdescent : baseEnd_5978346 < baseStart_5978346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978359 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 8]
def baseStart_5978359 : Nat := 118140960795 + 5978359 * 2 ^ 59
def prefixEnd_5978359 : Nat := 4983230072969 + 3 ^ 40 * 5978359 * 2
def baseEnd_5978359 : Nat := 3069771692132680376618533

theorem tailTrace_5978359 : CollatzResearch.WordTrace tailWord_5978359 prefixEnd_5978359 3069771692132680376618533 := by
  unfold tailWord_5978359
  simp only [CollatzResearch.WordTrace]
  refine ⟨218048666148433840274562131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145365777432289226849708087 218048666148433840274562131)
  ·
    refine ⟨327072999222650760411843197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218048666148433840274562131 327072999222650760411843197)
    ·
      refine ⟨122652374708494035154441199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327072999222650760411843197 122652374708494035154441199)
      ·
        refine ⟨183978562062741052731661799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122652374708494035154441199 183978562062741052731661799)
        ·
          refine ⟨275967843094111579097492699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183978562062741052731661799 275967843094111579097492699)
          ·
            refine ⟨413951764641167368646239049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275967843094111579097492699 413951764641167368646239049)
            ·
              refine ⟨310463823480875526484679287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413951764641167368646239049 310463823480875526484679287)
              ·
                refine ⟨465695735221313289727018931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310463823480875526484679287 465695735221313289727018931)
                ·
                  refine ⟨698543602831969934590528397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465695735221313289727018931 698543602831969934590528397)
                  ·
                    refine ⟨261953851061988725471448149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 698543602831969934590528397 261953851061988725471448149)
                    ·
                      refine ⟨3069771692132680376618533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 261953851061988725471448149 3069771692132680376618533)
                      ·
                        rfl

theorem cell23_5978359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_5978359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978359 prefixEnd_5978359 := by exact prefixLift 5978359
  have htrace : WordTrace (prefixWord ++ tailWord_5978359) baseStart_5978359 baseEnd_5978359 := by
    simpa [prefixWord, tailWord_5978359, baseEnd_5978359] using wordTrace_append hprefix tailTrace_5978359
  have hstable : (prefixWord ++ tailWord_5978359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978359).length < 2 ^ (prefixWord ++ tailWord_5978359).sum := by decide
  have hdescent : baseEnd_5978359 < baseStart_5978359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978367 : List Nat := [1, 1, 2, 2, 1, 4, 5, 1, 2, 2, 2]
def baseStart_5978367 : Nat := 118140960795 + 5978367 * 2 ^ 59
def prefixEnd_5978367 : Nat := 4983230072969 + 3 ^ 40 * 5978367 * 2
def baseEnd_5978367 : Nat := 3069775799977916345318497

theorem tailTrace_5978367 : CollatzResearch.WordTrace tailWord_5978367 prefixEnd_5978367 3069775799977916345318497 := by
  unfold tailWord_5978367
  simp only [CollatzResearch.WordTrace]
  refine ⟨218048957932404857640853355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145365971954936571760568903 218048957932404857640853355)
  ·
    refine ⟨327073436898607286461280033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218048957932404857640853355 327073436898607286461280033)
    ·
      refine ⟨245305077673955464845960025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327073436898607286461280033 245305077673955464845960025)
      ·
        refine ⟨183978808255466598634470019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245305077673955464845960025 183978808255466598634470019)
        ·
          refine ⟨275968212383199897951705029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183978808255466598634470019 275968212383199897951705029)
          ·
            refine ⟨51744039821849980865944693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 275968212383199897951705029 51744039821849980865944693)
            ·
              refine ⟨4851003733298435706182315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51744039821849980865944693 4851003733298435706182315)
              ·
                refine ⟨7276505599947653559273473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4851003733298435706182315 7276505599947653559273473)
                ·
                  refine ⟨5457379199960740169455105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7276505599947653559273473 5457379199960740169455105)
                  ·
                    refine ⟨4093034399970555127091329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5457379199960740169455105 4093034399970555127091329)
                    ·
                      refine ⟨3069775799977916345318497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4093034399970555127091329 3069775799977916345318497)
                      ·
                        rfl

theorem cell23_5978367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 2, 2, 2].length) (baseStart_5978367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978367 prefixEnd_5978367 := by exact prefixLift 5978367
  have htrace : WordTrace (prefixWord ++ tailWord_5978367) baseStart_5978367 baseEnd_5978367 := by
    simpa [prefixWord, tailWord_5978367, baseEnd_5978367] using wordTrace_append hprefix tailTrace_5978367
  have hstable : (prefixWord ++ tailWord_5978367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978367).length < 2 ^ (prefixWord ++ tailWord_5978367).sum := by decide
  have hdescent : baseEnd_5978367 < baseStart_5978367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978396 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_5978396 : Nat := 118140960795 + 5978396 * 2 ^ 59
def prefixEnd_5978396 : Nat := 4983230072969 + 3 ^ 40 * 5978396 * 2
def baseEnd_5978396 : Nat := 3069790690916896731855863

theorem tailTrace_5978396 : CollatzResearch.WordTrace tailWord_5978396 prefixEnd_5978396 3069790690916896731855863 := by
  unfold tailWord_5978396
  simp only [CollatzResearch.WordTrace]
  refine ⟨109025007824649897796829521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145366677099533197062439361 109025007824649897796829521)
  ·
    refine ⟨81768755868487423347622141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109025007824649897796829521 81768755868487423347622141)
    ·
      refine ⟨30663283450682783755358303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81768755868487423347622141 30663283450682783755358303)
      ·
        refine ⟨45994925176024175633037455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30663283450682783755358303 45994925176024175633037455)
        ·
          refine ⟨68992387764036263449556183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45994925176024175633037455 68992387764036263449556183)
          ·
            refine ⟨103488581646054395174334275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68992387764036263449556183 103488581646054395174334275)
            ·
              refine ⟨155232872469081592761501413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103488581646054395174334275 155232872469081592761501413)
              ·
                refine ⟨29106163587952798642781515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155232872469081592761501413 29106163587952798642781515)
                ·
                  refine ⟨43659245381929197964172273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29106163587952798642781515 43659245381929197964172273)
                  ·
                    refine ⟨32744434036446898473129205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43659245381929197964172273 32744434036446898473129205)
                    ·
                      refine ⟨3069790690916896731855863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32744434036446898473129205 3069790690916896731855863)
                      ·
                        rfl

theorem cell23_5978396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_5978396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978396 prefixEnd_5978396 := by exact prefixLift 5978396
  have htrace : WordTrace (prefixWord ++ tailWord_5978396) baseStart_5978396 baseEnd_5978396 := by
    simpa [prefixWord, tailWord_5978396, baseEnd_5978396] using wordTrace_append hprefix tailTrace_5978396
  have hstable : (prefixWord ++ tailWord_5978396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978396).length < 2 ^ (prefixWord ++ tailWord_5978396).sum := by decide
  have hdescent : baseEnd_5978396 < baseStart_5978396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978423 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 2, 4, 2]
def baseStart_5978423 : Nat := 118140960795 + 5978423 * 2 ^ 59
def prefixEnd_5978423 : Nat := 4983230072969 + 3 ^ 40 * 5978423 * 2
def baseEnd_5978423 : Nat := 3069804554894568126218239

theorem tailTrace_5978423 : CollatzResearch.WordTrace tailWord_5978423 prefixEnd_5978423 3069804554894568126218239 := by
  unfold tailWord_5978423
  simp only [CollatzResearch.WordTrace]
  refine ⟨218051000420201979204891923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145367333613467986136594615 218051000420201979204891923)
  ·
    refine ⟨327076500630302968807337885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218051000420201979204891923 327076500630302968807337885)
    ·
      refine ⟨122653687736363613302751707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327076500630302968807337885 122653687736363613302751707)
      ·
        refine ⟨183980531604545419954127561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122653687736363613302751707 183980531604545419954127561)
        ·
          refine ⟨137985398703409064965595671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183980531604545419954127561 137985398703409064965595671)
          ·
            refine ⟨206978098055113597448393507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137985398703409064965595671 206978098055113597448393507)
            ·
              refine ⟨310467147082670396172590261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206978098055113597448393507 310467147082670396172590261)
              ·
                refine ⟨29106295039000349641180337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 310467147082670396172590261 29106295039000349641180337)
                ·
                  refine ⟨21829721279250262230885253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29106295039000349641180337 21829721279250262230885253)
                  ·
                    refine ⟨4093072739859424168290985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21829721279250262230885253 4093072739859424168290985)
                    ·
                      refine ⟨3069804554894568126218239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4093072739859424168290985 3069804554894568126218239)
                      ·
                        rfl

theorem cell23_5978423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 4, 2].length) (baseStart_5978423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978423 prefixEnd_5978423 := by exact prefixLift 5978423
  have htrace : WordTrace (prefixWord ++ tailWord_5978423) baseStart_5978423 baseEnd_5978423 := by
    simpa [prefixWord, tailWord_5978423, baseEnd_5978423] using wordTrace_append hprefix tailTrace_5978423
  have hstable : (prefixWord ++ tailWord_5978423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978423).length < 2 ^ (prefixWord ++ tailWord_5978423).sum := by decide
  have hdescent : baseEnd_5978423 < baseStart_5978423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978446 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 8]
def baseStart_5978446 : Nat := 118140960795 + 5978446 * 2 ^ 59
def prefixEnd_5978446 : Nat := 4983230072969 + 3 ^ 40 * 5978446 * 2
def baseEnd_5978446 : Nat := 341090707216624615136737

theorem tailTrace_5978446 : CollatzResearch.WordTrace tailWord_5978446 prefixEnd_5978446 341090707216624615136737 := by
  unfold tailWord_5978446
  simp only [CollatzResearch.WordTrace]
  refine ⟨27256479912389831766622399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145367892866079102755319461 27256479912389831766622399)
  ·
    refine ⟨40884719868584747649933599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27256479912389831766622399 40884719868584747649933599)
    ·
      refine ⟨61327079802877121474900399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40884719868584747649933599 61327079802877121474900399)
      ·
        refine ⟨91990619704315682212350599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61327079802877121474900399 91990619704315682212350599)
        ·
          refine ⟨137985929556473523318525899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91990619704315682212350599 137985929556473523318525899)
          ·
            refine ⟨206978894334710284977788849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137985929556473523318525899 206978894334710284977788849)
            ·
              refine ⟨155234170751032713733341637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206978894334710284977788849 155234170751032713733341637)
              ·
                refine ⟨29106407015818633825001557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155234170751032713733341637 29106407015818633825001557)
                ·
                  refine ⟨341090707216624615136737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29106407015818633825001557 341090707216624615136737)
                  ·
                    rfl

theorem cell23_5978446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_5978446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978446 prefixEnd_5978446 := by exact prefixLift 5978446
  have htrace : WordTrace (prefixWord ++ tailWord_5978446) baseStart_5978446 baseEnd_5978446 := by
    simpa [prefixWord, tailWord_5978446, baseEnd_5978446] using wordTrace_append hprefix tailTrace_5978446
  have hstable : (prefixWord ++ tailWord_5978446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978446).length < 2 ^ (prefixWord ++ tailWord_5978446).sum := by decide
  have hdescent : baseEnd_5978446 < baseStart_5978446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978483 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 3, 5, 2]
def baseStart_5978483 : Nat := 118140960795 + 5978483 * 2 ^ 59
def prefixEnd_5978483 : Nat := 4983230072969 + 3 ^ 40 * 5978483 * 2
def baseEnd_5978483 : Nat := 3069835363733837891467963

theorem tailTrace_5978483 : CollatzResearch.WordTrace tailWord_5978483 prefixEnd_5978483 3069835363733837891467963 := by
  unfold tailWord_5978483
  simp only [CollatzResearch.WordTrace]
  refine ⟨218053188799984609452076103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145368792533323072968050735 218053188799984609452076103)
  ·
    refine ⟨327079783199976914178114155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218053188799984609452076103 327079783199976914178114155)
    ·
      refine ⟨490619674799965371267171233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327079783199976914178114155 490619674799965371267171233)
      ·
        refine ⟨367964756099974028450378425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490619674799965371267171233 367964756099974028450378425)
        ·
          refine ⟨275973567074980521337783819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367964756099974028450378425 275973567074980521337783819)
          ·
            refine ⟨413960350612470782006675729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275973567074980521337783819 413960350612470782006675729)
            ·
              refine ⟨310470262959353086505006797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413960350612470782006675729 310470262959353086505006797)
              ·
                refine ⟨116426348609757407439377549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310470262959353086505006797 116426348609757407439377549)
                ·
                  refine ⟨43659880728659027789766581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116426348609757407439377549 43659880728659027789766581)
                  ·
                    refine ⟨4093113818311783855290617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43659880728659027789766581 4093113818311783855290617)
                    ·
                      refine ⟨3069835363733837891467963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4093113818311783855290617 3069835363733837891467963)
                      ·
                        rfl

theorem cell23_5978483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 5, 2].length) (baseStart_5978483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978483 prefixEnd_5978483 := by exact prefixLift 5978483
  have htrace : WordTrace (prefixWord ++ tailWord_5978483) baseStart_5978483 baseEnd_5978483 := by
    simpa [prefixWord, tailWord_5978483, baseEnd_5978483] using wordTrace_append hprefix tailTrace_5978483
  have hstable : (prefixWord ++ tailWord_5978483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978483).length < 2 ^ (prefixWord ++ tailWord_5978483).sum := by decide
  have hdescent : baseEnd_5978483 < baseStart_5978483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978493 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 3, 5]
def baseStart_5978493 : Nat := 118140960795 + 5978493 * 2 ^ 59
def prefixEnd_5978493 : Nat := 4983230072969 + 3 ^ 40 * 5978493 * 2
def baseEnd_5978493 : Nat := 1023280166180127617447639

theorem tailTrace_5978493 : CollatzResearch.WordTrace tailWord_5978493 prefixEnd_5978493 1023280166180127617447639 := by
  unfold tailWord_5978493
  simp only [CollatzResearch.WordTrace]
  refine ⟨218053553529948381159940133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145369035686632254106626755 218053553529948381159940133)
  ·
    refine ⟨40885041286865321467488775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218053553529948381159940133 40885041286865321467488775)
    ·
      refine ⟨61327561930297982201233163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40885041286865321467488775 61327561930297982201233163)
      ·
        refine ⟨91991342895446973301849745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61327561930297982201233163 91991342895446973301849745)
        ·
          refine ⟨68993507171585229976387309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91991342895446973301849745 68993507171585229976387309)
          ·
            refine ⟨25872565189344461241145241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68993507171585229976387309 25872565189344461241145241)
            ·
              refine ⟨19404423892008345930858931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25872565189344461241145241 19404423892008345930858931)
              ·
                refine ⟨29106635838012518896288397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19404423892008345930858931 29106635838012518896288397)
                ·
                  refine ⟨10914988439254694586108149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29106635838012518896288397 10914988439254694586108149)
                  ·
                    refine ⟨1023280166180127617447639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10914988439254694586108149 1023280166180127617447639)
                    ·
                      rfl

theorem cell23_5978493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_5978493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978493 prefixEnd_5978493 := by exact prefixLift 5978493
  have htrace : WordTrace (prefixWord ++ tailWord_5978493) baseStart_5978493 baseEnd_5978493 := by
    simpa [prefixWord, tailWord_5978493, baseEnd_5978493] using wordTrace_append hprefix tailTrace_5978493
  have hstable : (prefixWord ++ tailWord_5978493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978493).length < 2 ^ (prefixWord ++ tailWord_5978493).sum := by decide
  have hdescent : baseEnd_5978493 < baseStart_5978493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978500 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 1, 5, 2]
def baseStart_5978500 : Nat := 118140960795 + 5978500 * 2 ^ 59
def prefixEnd_5978500 : Nat := 4983230072969 + 3 ^ 40 * 5978500 * 2
def baseEnd_5978500 : Nat := 3069844092904964324955385

theorem tailTrace_5978500 : CollatzResearch.WordTrace tailWord_5978500 prefixEnd_5978500 3069844092904964324955385 := by
  unfold tailWord_5978500
  simp only [CollatzResearch.WordTrace]
  refine ⟨109026904420461510677722477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145369205893948680903629969 109026904420461510677722477)
  ·
    refine ⟨40885089157673066504145929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109026904420461510677722477 40885089157673066504145929)
    ·
      refine ⟨30663816868254799878109447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40885089157673066504145929 30663816868254799878109447)
      ·
        refine ⟨45995725302382199817164171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30663816868254799878109447 45995725302382199817164171)
        ·
          refine ⟨68993587953573299725746257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45995725302382199817164171 68993587953573299725746257)
          ·
            refine ⟨51745190965179974794309693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68993587953573299725746257 51745190965179974794309693)
            ·
              refine ⟨19404446611942490547866135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51745190965179974794309693 19404446611942490547866135)
              ·
                refine ⟨29106669917913735821799203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19404446611942490547866135 29106669917913735821799203)
                ·
                  refine ⟨43660004876870603732698805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29106669917913735821799203 43660004876870603732698805)
                  ·
                    refine ⟨4093125457206619099940513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43660004876870603732698805 4093125457206619099940513)
                    ·
                      refine ⟨3069844092904964324955385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4093125457206619099940513 3069844092904964324955385)
                      ·
                        rfl

theorem cell23_5978500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_5978500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978500 prefixEnd_5978500 := by exact prefixLift 5978500
  have htrace : WordTrace (prefixWord ++ tailWord_5978500) baseStart_5978500 baseEnd_5978500 := by
    simpa [prefixWord, tailWord_5978500, baseEnd_5978500] using wordTrace_append hprefix tailTrace_5978500
  have hstable : (prefixWord ++ tailWord_5978500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978500).length < 2 ^ (prefixWord ++ tailWord_5978500).sum := by decide
  have hdescent : baseEnd_5978500 < baseStart_5978500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978507 : List Nat := [1, 1, 1, 1, 4, 4, 1, 5, 1, 1, 3]
def baseStart_5978507 : Nat := 118140960795 + 5978507 * 2 ^ 59
def prefixEnd_5978507 : Nat := 4983230072969 + 3 ^ 40 * 5978507 * 2
def baseEnd_5978507 : Nat := 3069847687269545797567853

theorem tailTrace_5978507 : CollatzResearch.WordTrace tailWord_5978507 prefixEnd_5978507 3069847687269545797567853 := by
  unfold tailWord_5978507
  simp only [CollatzResearch.WordTrace]
  refine ⟨218054064151897661550949775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145369376101265107700633183 218054064151897661550949775)
  ·
    refine ⟨327081096227846492326424663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218054064151897661550949775 327081096227846492326424663)
    ·
      refine ⟨490621644341769738489636995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327081096227846492326424663 490621644341769738489636995)
      ·
        refine ⟨735932466512654607734455493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490621644341769738489636995 735932466512654607734455493)
        ·
          refine ⟨137987337471122738950210405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 735932466512654607734455493 137987337471122738950210405)
          ·
            refine ⟨25872625775835513553164451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137987337471122738950210405 25872625775835513553164451)
            ·
              refine ⟨38808938663753270329746677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25872625775835513553164451 38808938663753270329746677)
              ·
                refine ⟨3638337999726869093413751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38808938663753270329746677 3638337999726869093413751)
                ·
                  refine ⟨5457506999590303640120627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3638337999726869093413751 5457506999590303640120627)
                  ·
                    refine ⟨8186260499385455460180941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5457506999590303640120627 8186260499385455460180941)
                    ·
                      refine ⟨3069847687269545797567853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8186260499385455460180941 3069847687269545797567853)
                      ·
                        rfl

theorem cell23_5978507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 1, 1, 3].length) (baseStart_5978507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978507 prefixEnd_5978507 := by exact prefixLift 5978507
  have htrace : WordTrace (prefixWord ++ tailWord_5978507) baseStart_5978507 baseEnd_5978507 := by
    simpa [prefixWord, tailWord_5978507, baseEnd_5978507] using wordTrace_append hprefix tailTrace_5978507
  have hstable : (prefixWord ++ tailWord_5978507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978507).length < 2 ^ (prefixWord ++ tailWord_5978507).sum := by decide
  have hdescent : baseEnd_5978507 < baseStart_5978507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978533 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 1, 1, 5]
def baseStart_5978533 : Nat := 118140960795 + 5978533 * 2 ^ 59
def prefixEnd_5978533 : Nat := 4983230072969 + 3 ^ 40 * 5978533 * 2
def baseEnd_5978533 : Nat := 3069861037766562695842733

theorem tailTrace_5978533 : CollatzResearch.WordTrace tailWord_5978533 prefixEnd_5978533 3069861037766562695842733 := by
  unfold tailWord_5978533
  simp only [CollatzResearch.WordTrace]
  refine ⟨218055012449803467991396253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145370008299868978660930835 218055012449803467991396253)
  ·
    refine ⟨81770629668676300496773595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218055012449803467991396253 81770629668676300496773595)
    ·
      refine ⟨122655944503014450745160393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81770629668676300496773595 122655944503014450745160393)
      ·
        refine ⟨91991958377260838058870295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122655944503014450745160393 91991958377260838058870295)
        ·
          refine ⟨137987937565891257088305443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91991958377260838058870295 137987937565891257088305443)
          ·
            refine ⟨206981906348836885632458165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137987937565891257088305443 206981906348836885632458165)
            ·
              refine ⟨19404553720203458028042953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 206981906348836885632458165 19404553720203458028042953)
              ·
                refine ⟨14553415290152593521032215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19404553720203458028042953 14553415290152593521032215)
                ·
                  refine ⟨21830122935228890281548323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14553415290152593521032215 21830122935228890281548323)
                  ·
                    refine ⟨32745184402843335422322485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21830122935228890281548323 32745184402843335422322485)
                    ·
                      refine ⟨3069861037766562695842733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32745184402843335422322485 3069861037766562695842733)
                      ·
                        rfl

theorem cell23_5978533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_5978533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978533 prefixEnd_5978533 := by exact prefixLift 5978533
  have htrace : WordTrace (prefixWord ++ tailWord_5978533) baseStart_5978533 baseEnd_5978533 := by
    simpa [prefixWord, tailWord_5978533, baseEnd_5978533] using wordTrace_append hprefix tailTrace_5978533
  have hstable : (prefixWord ++ tailWord_5978533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978533).length < 2 ^ (prefixWord ++ tailWord_5978533).sum := by decide
  have hdescent : baseEnd_5978533 < baseStart_5978533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978553 : List Nat := [1, 2, 1, 4, 3, 2, 1, 9]
def baseStart_5978553 : Nat := 118140960795 + 5978553 * 2 ^ 59
def prefixEnd_5978553 : Nat := 4983230072969 + 3 ^ 40 * 5978553 * 2
def baseEnd_5978553 : Nat := 113698937310357504355283

theorem tailTrace_5978553 : CollatzResearch.WordTrace tailWord_5978553 prefixEnd_5978553 113698937310357504355283 := by
  unfold tailWord_5978553
  simp only [CollatzResearch.WordTrace]
  refine ⟨218055741909731011407124313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145370494606487340938082875 218055741909731011407124313)
  ·
    refine ⟨163541806432298258555343235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218055741909731011407124313 163541806432298258555343235)
    ·
      refine ⟨245312709648447387833014853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163541806432298258555343235 245312709648447387833014853)
      ·
        refine ⟨45996133059083885218690285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245312709648447387833014853 45996133059083885218690285)
        ·
          refine ⟨17248549897156456957008857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45996133059083885218690285 17248549897156456957008857)
          ·
            refine ⟨12936412422867342717756643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17248549897156456957008857 12936412422867342717756643)
            ·
              refine ⟨19404618634301014076634965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12936412422867342717756643 19404618634301014076634965)
              ·
                refine ⟨113698937310357504355283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19404618634301014076634965 113698937310357504355283)
                ·
                  rfl

theorem cell23_5978553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 9].length) (baseStart_5978553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978553 prefixEnd_5978553 := by exact prefixLift 5978553
  have htrace : WordTrace (prefixWord ++ tailWord_5978553) baseStart_5978553 baseEnd_5978553 := by
    simpa [prefixWord, tailWord_5978553, baseEnd_5978553] using wordTrace_append hprefix tailTrace_5978553
  have hstable : (prefixWord ++ tailWord_5978553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978553).length < 2 ^ (prefixWord ++ tailWord_5978553).sum := by decide
  have hdescent : baseEnd_5978553 < baseStart_5978553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978563 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 3]
def baseStart_5978563 : Nat := 118140960795 + 5978563 * 2 ^ 59
def prefixEnd_5978563 : Nat := 4983230072969 + 3 ^ 40 * 5978563 * 2
def baseEnd_5978563 : Nat := 3069876442186197578467595

theorem tailTrace_5978563 : CollatzResearch.WordTrace tailWord_5978563 prefixEnd_5978563 3069876442186197578467595 := by
  unfold tailWord_5978563
  simp only [CollatzResearch.WordTrace]
  refine ⟨218056106639694783114988343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145370737759796522076658895 218056106639694783114988343)
  ·
    refine ⟨327084159959542174672482515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218056106639694783114988343 327084159959542174672482515)
    ·
      refine ⟨490626239939313262008723773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327084159959542174672482515 490626239939313262008723773)
      ·
        refine ⟨183984839977242473253271415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 490626239939313262008723773 183984839977242473253271415)
        ·
          refine ⟨275977259965863709879907123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183984839977242473253271415 275977259965863709879907123)
          ·
            refine ⟨413965889948795564819860685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275977259965863709879907123 413965889948795564819860685)
            ·
              refine ⟨155237208730798336807447757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 413965889948795564819860685 155237208730798336807447757)
              ·
                refine ⟨58213953274049376302792909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155237208730798336807447757 58213953274049376302792909)
                ·
                  refine ⟨21830232477768516113547341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58213953274049376302792909 21830232477768516113547341)
                  ·
                    refine ⟨8186337179163193542580253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21830232477768516113547341 8186337179163193542580253)
                    ·
                      refine ⟨3069876442186197578467595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8186337179163193542580253 3069876442186197578467595)
                      ·
                        rfl

theorem cell23_5978563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_5978563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978563 prefixEnd_5978563 := by exact prefixLift 5978563
  have htrace : WordTrace (prefixWord ++ tailWord_5978563) baseStart_5978563 baseEnd_5978563 := by
    simpa [prefixWord, tailWord_5978563, baseEnd_5978563] using wordTrace_append hprefix tailTrace_5978563
  have hstable : (prefixWord ++ tailWord_5978563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978563).length < 2 ^ (prefixWord ++ tailWord_5978563).sum := by decide
  have hdescent : baseEnd_5978563 < baseStart_5978563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978623 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 5]
def baseStart_5978623 : Nat := 118140960795 + 5978623 * 2 ^ 59
def prefixEnd_5978623 : Nat := 4983230072969 + 3 ^ 40 * 5978623 * 2
def baseEnd_5978623 : Nat := 3069907251025467343717319

theorem tailTrace_5978623 : CollatzResearch.WordTrace tailWord_5978623 prefixEnd_5978623 3069907251025467343717319 := by
  unfold tailWord_5978623
  simp only [CollatzResearch.WordTrace]
  refine ⟨218058295019477413362172523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145372196679651608908115015 218058295019477413362172523)
  ·
    refine ⟨327087442529216120043258785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218058295019477413362172523 327087442529216120043258785)
    ·
      refine ⟨245315581896912090032444089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327087442529216120043258785 245315581896912090032444089)
      ·
        refine ⟨183986686422684067524333067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245315581896912090032444089 183986686422684067524333067)
        ·
          refine ⟨275980029634026101286499601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183986686422684067524333067 275980029634026101286499601)
          ·
            refine ⟨206985022225519575964874701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275980029634026101286499601 206985022225519575964874701)
            ·
              refine ⟨77619383334569840986828013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206985022225519575964874701 77619383334569840986828013)
              ·
                refine ⟨29107268750463690370060505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77619383334569840986828013 29107268750463690370060505)
                ·
                  refine ⟨21830451562847767777545379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29107268750463690370060505 21830451562847767777545379)
                  ·
                    refine ⟨32745677344271651666318069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21830451562847767777545379 32745677344271651666318069)
                    ·
                      refine ⟨3069907251025467343717319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32745677344271651666318069 3069907251025467343717319)
                      ·
                        rfl

theorem cell23_5978623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_5978623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978623 prefixEnd_5978623 := by exact prefixLift 5978623
  have htrace : WordTrace (prefixWord ++ tailWord_5978623) baseStart_5978623 baseEnd_5978623 := by
    simpa [prefixWord, tailWord_5978623, baseEnd_5978623] using wordTrace_append hprefix tailTrace_5978623
  have hstable : (prefixWord ++ tailWord_5978623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978623).length < 2 ^ (prefixWord ++ tailWord_5978623).sum := by decide
  have hdescent : baseEnd_5978623 < baseStart_5978623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978643 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 7]
def baseStart_5978643 : Nat := 118140960795 + 5978643 * 2 ^ 59
def prefixEnd_5978643 : Nat := 4983230072969 + 3 ^ 40 * 5978643 * 2
def baseEnd_5978643 : Nat := 341101946737617473940803

theorem tailTrace_5978643 : CollatzResearch.WordTrace tailWord_5978643 prefixEnd_5978643 341101946737617473940803 := by
  unfold tailWord_5978643
  simp only [CollatzResearch.WordTrace]
  refine ⟨218059024479404956777900583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145372682986269971185267055 218059024479404956777900583)
  ·
    refine ⟨327088536719107435166850875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218059024479404956777900583 327088536719107435166850875)
    ·
      refine ⟨490632805078661152750276313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327088536719107435166850875 490632805078661152750276313)
      ·
        refine ⟨367974603808995864562707235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490632805078661152750276313 367974603808995864562707235)
        ·
          refine ⟨551961905713493796844060853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367974603808995864562707235 551961905713493796844060853)
          ·
            refine ⟨51746428660640043454130705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 551961905713493796844060853 51746428660640043454130705)
            ·
              refine ⟨38809821495480032590598029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51746428660640043454130705 38809821495480032590598029)
              ·
                refine ⟨14553683060805012221474261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38809821495480032590598029 14553683060805012221474261)
                ·
                  refine ⟨341101946737617473940803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14553683060805012221474261 341101946737617473940803)
                  ·
                    rfl

theorem cell23_5978643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 7].length) (baseStart_5978643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978643 prefixEnd_5978643 := by exact prefixLift 5978643
  have htrace : WordTrace (prefixWord ++ tailWord_5978643) baseStart_5978643 baseEnd_5978643 := by
    simpa [prefixWord, tailWord_5978643, baseEnd_5978643] using wordTrace_append hprefix tailTrace_5978643
  have hstable : (prefixWord ++ tailWord_5978643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978643).length < 2 ^ (prefixWord ++ tailWord_5978643).sum := by decide
  have hdescent : baseEnd_5978643 < baseStart_5978643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978647 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 2, 6]
def baseStart_5978647 : Nat := 118140960795 + 5978647 * 2 ^ 59
def prefixEnd_5978647 : Nat := 4983230072969 + 3 ^ 40 * 5978647 * 2
def baseEnd_5978647 : Nat := 1023306524853725083272403

theorem tailTrace_5978647 : CollatzResearch.WordTrace tailWord_5978647 prefixEnd_5978647 1023306524853725083272403 := by
  unfold tailWord_5978647
  simp only [CollatzResearch.WordTrace]
  refine ⟨218059170371390465461046195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145372780247593643640697463 218059170371390465461046195)
  ·
    refine ⟨327088755557085698191569293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218059170371390465461046195 327088755557085698191569293)
    ·
      refine ⟨122658283333907136821838485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327088755557085698191569293 122658283333907136821838485)
      ·
        refine ⟨5749607031276897038523679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122658283333907136821838485 5749607031276897038523679)
        ·
          refine ⟨8624410546915345557785519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5749607031276897038523679 8624410546915345557785519)
          ·
            refine ⟨12936615820373018336678279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8624410546915345557785519 12936615820373018336678279)
            ·
              refine ⟨19404923730559527505017419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12936615820373018336678279 19404923730559527505017419)
              ·
                refine ⟨29107385595839291257526129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19404923730559527505017419 29107385595839291257526129)
                ·
                  refine ⟨21830539196879468443144597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29107385595839291257526129 21830539196879468443144597)
                  ·
                    refine ⟨1023306524853725083272403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21830539196879468443144597 1023306524853725083272403)
                    ·
                      rfl

theorem cell23_5978647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_5978647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978647 prefixEnd_5978647 := by exact prefixLift 5978647
  have htrace : WordTrace (prefixWord ++ tailWord_5978647) baseStart_5978647 baseEnd_5978647 := by
    simpa [prefixWord, tailWord_5978647, baseEnd_5978647] using wordTrace_append hprefix tailTrace_5978647
  have hstable : (prefixWord ++ tailWord_5978647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978647).length < 2 ^ (prefixWord ++ tailWord_5978647).sum := by decide
  have hdescent : baseEnd_5978647 < baseStart_5978647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978677 : List Nat := [1, 3, 3, 1, 1, 2, 4, 3, 5]
def baseStart_5978677 : Nat := 118140960795 + 5978677 * 2 ^ 59
def prefixEnd_5978677 : Nat := 4983230072969 + 3 ^ 40 * 5978677 * 2
def baseEnd_5978677 : Nat := 341103886553423348049119

theorem tailTrace_5978677 : CollatzResearch.WordTrace tailWord_5978677 prefixEnd_5978677 341103886553423348049119 := by
  unfold tailWord_5978677
  simp only [CollatzResearch.WordTrace]
  refine ⟨218060264561281780584638285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145373509707521187056425523 218060264561281780584638285)
  ·
    refine ⟨81772599210480667719239357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218060264561281780584638285 81772599210480667719239357)
    ·
      refine ⟨30664724703930250394714759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81772599210480667719239357 30664724703930250394714759)
      ·
        refine ⟨45997087055895375592072139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30664724703930250394714759 45997087055895375592072139)
        ·
          refine ⟨68995630583843063388108209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45997087055895375592072139 68995630583843063388108209)
          ·
            refine ⟨51746722937882297541081157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68995630583843063388108209 51746722937882297541081157)
            ·
              refine ⟨9702510550852930788952717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51746722937882297541081157 9702510550852930788952717)
              ·
                refine ⟨3638441456569849045857269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9702510550852930788952717 3638441456569849045857269)
                ·
                  refine ⟨341103886553423348049119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3638441456569849045857269 341103886553423348049119)
                  ·
                    rfl

theorem cell23_5978677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 5].length) (baseStart_5978677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978677 prefixEnd_5978677 := by exact prefixLift 5978677
  have htrace : WordTrace (prefixWord ++ tailWord_5978677) baseStart_5978677 baseEnd_5978677 := by
    simpa [prefixWord, tailWord_5978677, baseEnd_5978677] using wordTrace_append hprefix tailTrace_5978677
  have hstable : (prefixWord ++ tailWord_5978677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978677).length < 2 ^ (prefixWord ++ tailWord_5978677).sum := by decide
  have hdescent : baseEnd_5978677 < baseStart_5978677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978694 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_5978694 : Nat := 118140960795 + 5978694 * 2 ^ 59
def prefixEnd_5978694 : Nat := 4983230072969 + 3 ^ 40 * 5978694 * 2
def baseEnd_5978694 : Nat := 341104856461326285103277

theorem tailTrace_5978694 : CollatzResearch.WordTrace tailWord_5978694 prefixEnd_5978694 341104856461326285103277 := by
  unfold tailWord_5978694
  simp only [CollatzResearch.WordTrace]
  refine ⟨6814402643819381015250223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145373923068146794992004757 6814402643819381015250223)
  ·
    refine ⟨10221603965729071522875335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6814402643819381015250223 10221603965729071522875335)
    ·
      refine ⟨15332405948593607284313003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10221603965729071522875335 15332405948593607284313003)
      ·
        refine ⟨22998608922890410926469505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15332405948593607284313003 22998608922890410926469505)
        ·
          refine ⟨17248956692167808194852129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22998608922890410926469505 17248956692167808194852129)
          ·
            refine ⟨12936717519125856146139097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17248956692167808194852129 12936717519125856146139097)
            ·
              refine ⟨9702538139344392109604323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12936717519125856146139097 9702538139344392109604323)
              ·
                refine ⟨14553807209016588164406485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9702538139344392109604323 14553807209016588164406485)
                ·
                  refine ⟨341104856461326285103277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14553807209016588164406485 341104856461326285103277)
                  ·
                    rfl

theorem cell23_5978694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_5978694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978694 prefixEnd_5978694 := by exact prefixLift 5978694
  have htrace : WordTrace (prefixWord ++ tailWord_5978694) baseStart_5978694 baseEnd_5978694 := by
    simpa [prefixWord, tailWord_5978694, baseEnd_5978694] using wordTrace_append hprefix tailTrace_5978694
  have hstable : (prefixWord ++ tailWord_5978694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978694).length < 2 ^ (prefixWord ++ tailWord_5978694).sum := by decide
  have hdescent : baseEnd_5978694 < baseStart_5978694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978777 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 5, 1, 3]
def baseStart_5978777 : Nat := 118140960795 + 5978777 * 2 ^ 59
def prefixEnd_5978777 : Nat := 4983230072969 + 3 ^ 40 * 5978777 * 2
def baseEnd_5978777 : Nat := 3069986327046259741191611

theorem tailTrace_5978777 : CollatzResearch.WordTrace tailWord_5978777 prefixEnd_5978777 3069986327046259741191611 := by
  unfold tailWord_5978777
  simp only [CollatzResearch.WordTrace]
  refine ⟨218063911860919497663278585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145375941240612998442185723 218063911860919497663278585)
  ·
    refine ⟨163547933895689623247458939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218063911860919497663278585 163547933895689623247458939)
    ·
      refine ⟨245321900843534434871188409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163547933895689623247458939 245321900843534434871188409)
      ·
        refine ⟨183991425632650826153391307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245321900843534434871188409 183991425632650826153391307)
        ·
          refine ⟨275987138448976239230086961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183991425632650826153391307 275987138448976239230086961)
          ·
            refine ⟨206990353836732179422565221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275987138448976239230086961 206990353836732179422565221)
            ·
              refine ⟨38810691344387283641730979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206990353836732179422565221 38810691344387283641730979)
              ·
                refine ⟨58216037016580925462596469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38810691344387283641730979 58216037016580925462596469)
                ·
                  refine ⟨5457753470304461762118419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58216037016580925462596469 5457753470304461762118419)
                  ·
                    refine ⟨8186630205456692643177629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5457753470304461762118419 8186630205456692643177629)
                    ·
                      refine ⟨3069986327046259741191611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8186630205456692643177629 3069986327046259741191611)
                      ·
                        rfl

theorem cell23_5978777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 1, 3].length) (baseStart_5978777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978777 prefixEnd_5978777 := by exact prefixLift 5978777
  have htrace : WordTrace (prefixWord ++ tailWord_5978777) baseStart_5978777 baseEnd_5978777 := by
    simpa [prefixWord, tailWord_5978777, baseEnd_5978777] using wordTrace_append hprefix tailTrace_5978777
  have hstable : (prefixWord ++ tailWord_5978777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978777).length < 2 ^ (prefixWord ++ tailWord_5978777).sum := by decide
  have hdescent : baseEnd_5978777 < baseStart_5978777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978810 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 3, 6]
def baseStart_5978810 : Nat := 118140960795 + 5978810 * 2 ^ 59
def prefixEnd_5978810 : Nat := 4983230072969 + 3 ^ 40 * 5978810 * 2
def baseEnd_5978810 : Nat := 1023334423969286037359653

theorem tailTrace_5978810 : CollatzResearch.WordTrace tailWord_5978810 prefixEnd_5978810 1023334423969286037359653 := by
  unfold tailWord_5978810
  simp only [CollatzResearch.WordTrace]
  refine ⟨54516278867449986074807471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145376743646533296199486589 54516278867449986074807471)
  ·
    refine ⟨81774418301174979112211207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54516278867449986074807471 81774418301174979112211207)
    ·
      refine ⟨122661627451762468668316811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81774418301174979112211207 122661627451762468668316811)
      ·
        refine ⟨183992441177643703002475217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122661627451762468668316811 183992441177643703002475217)
        ·
          refine ⟨137994330883232777251856413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183992441177643703002475217 137994330883232777251856413)
          ·
            refine ⟨51747874081212291469446155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137994330883232777251856413 51747874081212291469446155)
            ·
              refine ⟨77621811121818437204169233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51747874081212291469446155 77621811121818437204169233)
              ·
                refine ⟨58216358341363827903126925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77621811121818437204169233 58216358341363827903126925)
                ·
                  refine ⟨21831134378011435463672597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58216358341363827903126925 21831134378011435463672597)
                  ·
                    refine ⟨1023334423969286037359653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21831134378011435463672597 1023334423969286037359653)
                    ·
                      rfl

theorem cell23_5978810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_5978810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978810 prefixEnd_5978810 := by exact prefixLift 5978810
  have htrace : WordTrace (prefixWord ++ tailWord_5978810) baseStart_5978810 baseEnd_5978810 := by
    simpa [prefixWord, tailWord_5978810, baseEnd_5978810] using wordTrace_append hprefix tailTrace_5978810
  have hstable : (prefixWord ++ tailWord_5978810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978810).length < 2 ^ (prefixWord ++ tailWord_5978810).sum := by decide
  have hdescent : baseEnd_5978810 < baseStart_5978810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978844 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 1, 6]
def baseStart_5978844 : Nat := 118140960795 + 5978844 * 2 ^ 59
def prefixEnd_5978844 : Nat := 4983230072969 + 3 ^ 40 * 5978844 * 2
def baseEnd_5978844 : Nat := 1023340243416703659684601

theorem tailTrace_5978844 : CollatzResearch.WordTrace tailWord_5978844 prefixEnd_5978844 1023340243416703659684601 := by
  unfold tailWord_5978844
  simp only [CollatzResearch.WordTrace]
  refine ⟨109033177775838384052983793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145377570367784512070645057 109033177775838384052983793)
  ·
    refine ⟨81774883331878788039737845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109033177775838384052983793 81774883331878788039737845)
    ·
      refine ⟨7666395312363636378725423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81774883331878788039737845 7666395312363636378725423)
      ·
        refine ⟨11499592968545454568088135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7666395312363636378725423 11499592968545454568088135)
        ·
          refine ⟨17249389452818181852132203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11499592968545454568088135 17249389452818181852132203)
          ·
            refine ⟨25874084179227272778198305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17249389452818181852132203 25874084179227272778198305)
            ·
              refine ⟨19405563134420454583648729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25874084179227272778198305 19405563134420454583648729)
              ·
                refine ⟨14554172350815340937736547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19405563134420454583648729 14554172350815340937736547)
                ·
                  refine ⟨21831258526223011406604821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14554172350815340937736547 21831258526223011406604821)
                  ·
                    refine ⟨1023340243416703659684601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21831258526223011406604821 1023340243416703659684601)
                    ·
                      rfl

theorem cell23_5978844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_5978844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978844 prefixEnd_5978844 := by exact prefixLift 5978844
  have htrace : WordTrace (prefixWord ++ tailWord_5978844) baseStart_5978844 baseEnd_5978844 := by
    simpa [prefixWord, tailWord_5978844, baseEnd_5978844] using wordTrace_append hprefix tailTrace_5978844
  have hstable : (prefixWord ++ tailWord_5978844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978844).length < 2 ^ (prefixWord ++ tailWord_5978844).sum := by decide
  have hdescent : baseEnd_5978844 < baseStart_5978844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978847 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 4]
def baseStart_5978847 : Nat := 118140960795 + 5978847 * 2 ^ 59
def prefixEnd_5978847 : Nat := 4983230072969 + 3 ^ 40 * 5978847 * 2
def baseEnd_5978847 : Nat := 3070022270692074467316289

theorem tailTrace_5978847 : CollatzResearch.WordTrace tailWord_5978847 prefixEnd_5978847 3070022270692074467316289 := by
  unfold tailWord_5978847
  simp only [CollatzResearch.WordTrace]
  refine ⟨218066464970665899618326795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145377643313777266412217863 218066464970665899618326795)
  ·
    refine ⟨327099697455998849427490193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218066464970665899618326795 327099697455998849427490193)
    ·
      refine ⟨245324773091999137070617645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327099697455998849427490193 245324773091999137070617645)
      ·
        refine ⟨91996789909499676401481617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245324773091999137070617645 91996789909499676401481617)
        ·
          refine ⟨68997592432124757301111213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91996789909499676401481617 68997592432124757301111213)
          ·
            refine ⟨25874097162046783987916705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68997592432124757301111213 25874097162046783987916705)
            ·
              refine ⟨19405572871535087990937529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25874097162046783987916705 19405572871535087990937529)
              ·
                refine ⟨14554179653651315993203147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19405572871535087990937529 14554179653651315993203147)
                ·
                  refine ⟨21831269480476973989804721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14554179653651315993203147 21831269480476973989804721)
                  ·
                    refine ⟨16373452110357730492353541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21831269480476973989804721 16373452110357730492353541)
                    ·
                      refine ⟨3070022270692074467316289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16373452110357730492353541 3070022270692074467316289)
                      ·
                        rfl

theorem cell23_5978847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_5978847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978847 prefixEnd_5978847 := by exact prefixLift 5978847
  have htrace : WordTrace (prefixWord ++ tailWord_5978847) baseStart_5978847 baseEnd_5978847 := by
    simpa [prefixWord, tailWord_5978847, baseEnd_5978847] using wordTrace_append hprefix tailTrace_5978847
  have hstable : (prefixWord ++ tailWord_5978847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978847).length < 2 ^ (prefixWord ++ tailWord_5978847).sum := by decide
  have hdescent : baseEnd_5978847 < baseStart_5978847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978851 : List Nat := [1, 1, 1, 7, 1, 1, 4, 1, 1, 1, 4]
def baseStart_5978851 : Nat := 118140960795 + 5978851 * 2 ^ 59
def prefixEnd_5978851 : Nat := 4983230072969 + 3 ^ 40 * 5978851 * 2
def baseEnd_5978851 : Nat := 3070024324614692451666271

theorem tailTrace_5978851 : CollatzResearch.WordTrace tailWord_5978851 prefixEnd_5978851 3070024324614692451666271 := by
  unfold tailWord_5978851
  simp only [CollatzResearch.WordTrace]
  refine ⟨218066610862651408301472407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145377740575100938867648271 218066610862651408301472407)
  ·
    refine ⟨327099916293977112452208611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218066610862651408301472407 327099916293977112452208611)
    ·
      refine ⟨490649874440965668678312917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327099916293977112452208611 490649874440965668678312917)
      ·
        refine ⟨11499606432210132859647959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 490649874440965668678312917 11499606432210132859647959)
        ·
          refine ⟨17249409648315199289471939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11499606432210132859647959 17249409648315199289471939)
          ·
            refine ⟨25874114472472798934207909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17249409648315199289471939 25874114472472798934207909)
            ·
              refine ⟨4851396463588649800163983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25874114472472798934207909 4851396463588649800163983)
              ·
                refine ⟨7277094695382974700245975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4851396463588649800163983 7277094695382974700245975)
                ·
                  refine ⟨10915642043074462050368963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7277094695382974700245975 10915642043074462050368963)
                  ·
                    refine ⟨16373463064611693075553445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10915642043074462050368963 16373463064611693075553445)
                    ·
                      refine ⟨3070024324614692451666271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16373463064611693075553445 3070024324614692451666271)
                      ·
                        rfl

theorem cell23_5978851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_5978851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978851 prefixEnd_5978851 := by exact prefixLift 5978851
  have htrace : WordTrace (prefixWord ++ tailWord_5978851) baseStart_5978851 baseEnd_5978851 := by
    simpa [prefixWord, tailWord_5978851, baseEnd_5978851] using wordTrace_append hprefix tailTrace_5978851
  have hstable : (prefixWord ++ tailWord_5978851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978851).length < 2 ^ (prefixWord ++ tailWord_5978851).sum := by decide
  have hdescent : baseEnd_5978851 < baseStart_5978851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978860 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 6]
def baseStart_5978860 : Nat := 118140960795 + 5978860 * 2 ^ 59
def prefixEnd_5978860 : Nat := 4983230072969 + 3 ^ 40 * 5978860 * 2
def baseEnd_5978860 : Nat := 3070028945940582916453729

theorem tailTrace_5978860 : CollatzResearch.WordTrace tailWord_5978860 prefixEnd_5978860 3070028945940582916453729 := by
  unfold tailWord_5978860
  simp only [CollatzResearch.WordTrace]
  refine ⟨109033469559809401419275017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145377959413079201892366689 109033469559809401419275017)
  ·
    refine ⟨81775102169857051064456263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109033469559809401419275017 81775102169857051064456263)
    ·
      refine ⟨122662653254785576596684395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81775102169857051064456263 122662653254785576596684395)
      ·
        refine ⟨183993979882178364895026593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122662653254785576596684395 183993979882178364895026593)
        ·
          refine ⟨137995484911633773671269945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183993979882178364895026593 137995484911633773671269945)
          ·
            refine ⟨103496613683725330253452459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137995484911633773671269945 103496613683725330253452459)
            ·
              refine ⟨155244920525587995380178689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103496613683725330253452459 155244920525587995380178689)
              ·
                refine ⟨116433690394190996535134017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155244920525587995380178689 116433690394190996535134017)
                ·
                  refine ⟨87325267795643247401350513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116433690394190996535134017 87325267795643247401350513)
                  ·
                    refine ⟨65493950846732435551012885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87325267795643247401350513 65493950846732435551012885)
                    ·
                      refine ⟨3070028945940582916453729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65493950846732435551012885 3070028945940582916453729)
                      ·
                        rfl

theorem cell23_5978860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_5978860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978860 prefixEnd_5978860 := by exact prefixLift 5978860
  have htrace : WordTrace (prefixWord ++ tailWord_5978860) baseStart_5978860 baseEnd_5978860 := by
    simpa [prefixWord, tailWord_5978860, baseEnd_5978860] using wordTrace_append hprefix tailTrace_5978860
  have hstable : (prefixWord ++ tailWord_5978860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978860).length < 2 ^ (prefixWord ++ tailWord_5978860).sum := by decide
  have hdescent : baseEnd_5978860 < baseStart_5978860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978878 : List Nat := [4, 2, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_5978878 : Nat := 118140960795 + 5978878 * 2 ^ 59
def prefixEnd_5978878 : Nat := 4983230072969 + 3 ^ 40 * 5978878 * 2
def baseEnd_5978878 : Nat := 1023346062864121282009549

theorem tailTrace_5978878 : CollatzResearch.WordTrace tailWord_5978878 prefixEnd_5978878 1023346062864121282009549 := by
  unfold tailWord_5978878
  simp only [CollatzResearch.WordTrace]
  refine ⟨27258449454194198989088161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145378397089035727941803525 27258449454194198989088161)
  ·
    refine ⟨20443837090645649241816121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27258449454194198989088161 20443837090645649241816121)
    ·
      refine ⟨15332877817984236931362091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20443837090645649241816121 15332877817984236931362091)
      ·
        refine ⟨22999316726976355397043137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15332877817984236931362091 22999316726976355397043137)
        ·
          refine ⟨17249487545232266547782353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22999316726976355397043137 17249487545232266547782353)
          ·
            refine ⟨12937115658924199910836765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17249487545232266547782353 12937115658924199910836765)
            ·
              refine ⟨4851418372096574966563787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12937115658924199910836765 4851418372096574966563787)
              ·
                refine ⟨7277127558144862449845681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4851418372096574966563787 7277127558144862449845681)
                ·
                  refine ⟨5457845668608646837384261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7277127558144862449845681 5457845668608646837384261)
                  ·
                    refine ⟨1023346062864121282009549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5457845668608646837384261 1023346062864121282009549)
                    ·
                      rfl

theorem cell23_5978878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_5978878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978878 prefixEnd_5978878 := by exact prefixLift 5978878
  have htrace : WordTrace (prefixWord ++ tailWord_5978878) baseStart_5978878 baseEnd_5978878 := by
    simpa [prefixWord, tailWord_5978878, baseEnd_5978878] using wordTrace_append hprefix tailTrace_5978878
  have hstable : (prefixWord ++ tailWord_5978878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978878).length < 2 ^ (prefixWord ++ tailWord_5978878).sum := by decide
  have hdescent : baseEnd_5978878 < baseStart_5978878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978880 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 5]
def baseStart_5978880 : Nat := 118140960795 + 5978880 * 2 ^ 59
def prefixEnd_5978880 : Nat := 4983230072969 + 3 ^ 40 * 5978880 * 2
def baseEnd_5978880 : Nat := 3070039215553672838203637

theorem tailTrace_5978880 : CollatzResearch.WordTrace tailWord_5978880 prefixEnd_5978880 3070039215553672838203637 := by
  unfold tailWord_5978880
  simp only [CollatzResearch.WordTrace]
  refine ⟨109033834289773173127139047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145378445719697564169518729 109033834289773173127139047)
  ·
    refine ⟨163550751434659759690708571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109033834289773173127139047 163550751434659759690708571)
    ·
      refine ⟨245326127151989639536062857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163550751434659759690708571 245326127151989639536062857)
      ·
        refine ⟨183994595363992229652047143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245326127151989639536062857 183994595363992229652047143)
        ·
          refine ⟨275991893045988344478070715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183994595363992229652047143 275991893045988344478070715)
          ·
            refine ⟨413987839568982516717106073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275991893045988344478070715 413987839568982516717106073)
            ·
              refine ⟨310490879676736887537829555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413987839568982516717106073 310490879676736887537829555)
              ·
                refine ⟨465736319515105331306744333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310490879676736887537829555 465736319515105331306744333)
                ·
                  refine ⟨174651119818164499240029125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 465736319515105331306744333 174651119818164499240029125)
                  ·
                    refine ⟨32747084965905843607505461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 174651119818164499240029125 32747084965905843607505461)
                    ·
                      refine ⟨3070039215553672838203637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32747084965905843607505461 3070039215553672838203637)
                      ·
                        rfl

theorem cell23_5978880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_5978880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978880 prefixEnd_5978880 := by exact prefixLift 5978880
  have htrace : WordTrace (prefixWord ++ tailWord_5978880) baseStart_5978880 baseEnd_5978880 := by
    simpa [prefixWord, tailWord_5978880, baseEnd_5978880] using wordTrace_append hprefix tailTrace_5978880
  have hstable : (prefixWord ++ tailWord_5978880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978880).length < 2 ^ (prefixWord ++ tailWord_5978880).sum := by decide
  have hdescent : baseEnd_5978880 < baseStart_5978880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978911 : List Nat := [1, 1, 2, 4, 2, 2, 2, 3, 1, 3, 2]
def baseStart_5978911 : Nat := 118140960795 + 5978911 * 2 ^ 59
def prefixEnd_5978911 : Nat := 4983230072969 + 3 ^ 40 * 5978911 * 2
def baseEnd_5978911 : Nat := 3070055133453962216915995

theorem tailTrace_5978911 : CollatzResearch.WordTrace tailWord_5978911 prefixEnd_5978911 3070055133453962216915995 := by
  unfold tailWord_5978911
  simp only [CollatzResearch.WordTrace]
  refine ⟨218068799242434038548656587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145379199494956025699104391 218068799242434038548656587)
  ·
    refine ⟨327103198863651057822984881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218068799242434038548656587 327103198863651057822984881)
    ·
      refine ⟨245327399147738293367238661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327103198863651057822984881 245327399147738293367238661)
      ·
        refine ⟨45998887340200930006357249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245327399147738293367238661 45998887340200930006357249)
        ·
          refine ⟨34499165505150697504767937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45998887340200930006357249 34499165505150697504767937)
          ·
            refine ⟨25874374128863023128575953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34499165505150697504767937 25874374128863023128575953)
            ·
              refine ⟨19405780596647267346431965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25874374128863023128575953 19405780596647267346431965)
              ·
                refine ⟨7277167723742725254911987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19405780596647267346431965 7277167723742725254911987)
                ·
                  refine ⟨10915751585614087882367981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7277167723742725254911987 10915751585614087882367981)
                  ·
                    refine ⟨4093406844605282955887993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10915751585614087882367981 4093406844605282955887993)
                    ·
                      refine ⟨3070055133453962216915995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4093406844605282955887993 3070055133453962216915995)
                      ·
                        rfl

theorem cell23_5978911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_5978911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978911 prefixEnd_5978911 := by exact prefixLift 5978911
  have htrace : WordTrace (prefixWord ++ tailWord_5978911) baseStart_5978911 baseEnd_5978911 := by
    simpa [prefixWord, tailWord_5978911, baseEnd_5978911] using wordTrace_append hprefix tailTrace_5978911
  have hstable : (prefixWord ++ tailWord_5978911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978911).length < 2 ^ (prefixWord ++ tailWord_5978911).sum := by decide
  have hdescent : baseEnd_5978911 < baseStart_5978911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978977 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 4, 5]
def baseStart_5978977 : Nat := 118140960795 + 5978977 * 2 ^ 59
def prefixEnd_5978977 : Nat := 4983230072969 + 3 ^ 40 * 5978977 * 2
def baseEnd_5978977 : Nat := 1023363007725719652896897

theorem tailTrace_5978977 : CollatzResearch.WordTrace tailWord_5978977 prefixEnd_5978977 1023363007725719652896897 := by
  unfold tailWord_5978977
  simp only [CollatzResearch.WordTrace]
  refine ⟨218071206460194931820559185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145380804306796621213706123 218071206460194931820559185)
  ·
    refine ⟨163553404845146198865419389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218071206460194931820559185 163553404845146198865419389)
    ·
      refine ⟨61332526816929824574532271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163553404845146198865419389 61332526816929824574532271)
      ·
        refine ⟨91998790225394736861798407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61332526816929824574532271 91998790225394736861798407)
        ·
          refine ⟨137998185338092105292697611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91998790225394736861798407 137998185338092105292697611)
          ·
            refine ⟨206997278007138157939046417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137998185338092105292697611 206997278007138157939046417)
            ·
              refine ⟨155247958505353618454284813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206997278007138157939046417 155247958505353618454284813)
              ·
                refine ⟨58217984439507606920356805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155247958505353618454284813 58217984439507606920356805)
                ·
                  refine ⟨10915872082407676297566901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58217984439507606920356805 10915872082407676297566901)
                  ·
                    refine ⟨1023363007725719652896897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10915872082407676297566901 1023363007725719652896897)
                    ·
                      rfl

theorem cell23_5978977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_5978977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978977 prefixEnd_5978977 := by exact prefixLift 5978977
  have htrace : WordTrace (prefixWord ++ tailWord_5978977) baseStart_5978977 baseEnd_5978977 := by
    simpa [prefixWord, tailWord_5978977, baseEnd_5978977] using wordTrace_append hprefix tailTrace_5978977
  have hstable : (prefixWord ++ tailWord_5978977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978977).length < 2 ^ (prefixWord ++ tailWord_5978977).sum := by decide
  have hdescent : baseEnd_5978977 < baseStart_5978977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978981 : List Nat := [1, 3, 1, 3, 1, 1, 6, 2, 5]
def baseStart_5978981 : Nat := 118140960795 + 5978981 * 2 ^ 59
def prefixEnd_5978981 : Nat := 4983230072969 + 3 ^ 40 * 5978981 * 2
def baseEnd_5978981 : Nat := 341121230788864104782297

theorem tailTrace_5978981 : CollatzResearch.WordTrace tailWord_5978981 prefixEnd_5978981 341121230788864104782297 := by
  unfold tailWord_5978981
  simp only [CollatzResearch.WordTrace]
  refine ⟨218071352352180440503704797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145380901568120293669136531 218071352352180440503704797)
  ·
    refine ⟨81776757132067665188889299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218071352352180440503704797 81776757132067665188889299)
    ·
      refine ⟨122665135698101497783333949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81776757132067665188889299 122665135698101497783333949)
      ·
        refine ⟨45999425886788061668750231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122665135698101497783333949 45999425886788061668750231)
        ·
          refine ⟨68999138830182092503125347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45999425886788061668750231 68999138830182092503125347)
          ·
            refine ⟨103498708245273138754688021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68999138830182092503125347 103498708245273138754688021)
            ·
              refine ⟨4851501948997178379126001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103498708245273138754688021 4851501948997178379126001)
              ·
                refine ⟨3638626461747883784344501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4851501948997178379126001 3638626461747883784344501)
                ·
                  refine ⟨341121230788864104782297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3638626461747883784344501 341121230788864104782297)
                  ·
                    rfl

theorem cell23_5978981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 5].length) (baseStart_5978981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978981 prefixEnd_5978981 := by exact prefixLift 5978981
  have htrace : WordTrace (prefixWord ++ tailWord_5978981) baseStart_5978981 baseEnd_5978981 := by
    simpa [prefixWord, tailWord_5978981, baseEnd_5978981] using wordTrace_append hprefix tailTrace_5978981
  have hstable : (prefixWord ++ tailWord_5978981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978981).length < 2 ^ (prefixWord ++ tailWord_5978981).sum := by decide
  have hdescent : baseEnd_5978981 < baseStart_5978981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5978987 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 5]
def baseStart_5978987 : Nat := 118140960795 + 5978987 * 2 ^ 59
def prefixEnd_5978987 : Nat := 4983230072969 + 3 ^ 40 * 5978987 * 2
def baseEnd_5978987 : Nat := 3070094157983703919565645

theorem tailTrace_5978987 : CollatzResearch.WordTrace tailWord_5978987 prefixEnd_5978987 3070094157983703919565645 := by
  unfold tailWord_5978987
  simp only [CollatzResearch.WordTrace]
  refine ⟨218071571190158703528423215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145381047460105802352282143 218071571190158703528423215)
  ·
    refine ⟨327107356785238055292634823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218071571190158703528423215 327107356785238055292634823)
    ·
      refine ⟨490661035177857082938952235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327107356785238055292634823 490661035177857082938952235)
      ·
        refine ⟨735991552766785624408428353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490661035177857082938952235 735991552766785624408428353)
        ·
          refine ⟨551993664575089218306321265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 735991552766785624408428353 551993664575089218306321265)
          ·
            refine ⟨413995248431316913729740949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551993664575089218306321265 413995248431316913729740949)
            ·
              refine ⟨19406027270217980331081607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 413995248431316913729740949 19406027270217980331081607)
              ·
                refine ⟨29109040905326970496622411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19406027270217980331081607 29109040905326970496622411)
                ·
                  refine ⟨43663561357990455744933617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29109040905326970496622411 43663561357990455744933617)
                  ·
                    refine ⟨32747671018492841808700213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43663561357990455744933617 32747671018492841808700213)
                    ·
                      refine ⟨3070094157983703919565645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32747671018492841808700213 3070094157983703919565645)
                      ·
                        rfl

theorem cell23_5978987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 5].length) (baseStart_5978987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5978987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5978987 prefixEnd_5978987 := by exact prefixLift 5978987
  have htrace : WordTrace (prefixWord ++ tailWord_5978987) baseStart_5978987 baseEnd_5978987 := by
    simpa [prefixWord, tailWord_5978987, baseEnd_5978987] using wordTrace_append hprefix tailTrace_5978987
  have hstable : (prefixWord ++ tailWord_5978987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5978987).length < 2 ^ (prefixWord ++ tailWord_5978987).sum := by decide
  have hdescent : baseEnd_5978987 < baseStart_5978987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5978987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979041 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 3, 4]
def baseStart_5979041 : Nat := 118140960795 + 5979041 * 2 ^ 59
def prefixEnd_5979041 : Nat := 4983230072969 + 3 ^ 40 * 5979041 * 2
def baseEnd_5979041 : Nat := 1023373961979682236096799

theorem tailTrace_5979041 : CollatzResearch.WordTrace tailWord_5979041 prefixEnd_5979041 1023373961979682236096799 := by
  unfold tailWord_5979041
  simp only [CollatzResearch.WordTrace]
  refine ⟨218073540731963070750888977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145382360487975380500592651 218073540731963070750888977)
  ·
    refine ⟨163555155548972303063166733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218073540731963070750888977 163555155548972303063166733)
    ·
      refine ⟨61333183330864613648687525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163555155548972303063166733 61333183330864613648687525)
      ·
        refine ⟨11499971874537115059128911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61333183330864613648687525 11499971874537115059128911)
        ·
          refine ⟨17249957811805672588693367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11499971874537115059128911 17249957811805672588693367)
          ·
            refine ⟨25874936717708508883040051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17249957811805672588693367 25874936717708508883040051)
            ·
              refine ⟨38812405076562763324560077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25874936717708508883040051 38812405076562763324560077)
              ·
                refine ⟨14554651903711036246710029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38812405076562763324560077 14554651903711036246710029)
                ·
                  refine ⟨5457994463891638592516261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14554651903711036246710029 5457994463891638592516261)
                  ·
                    refine ⟨1023373961979682236096799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5457994463891638592516261 1023373961979682236096799)
                    ·
                      rfl

theorem cell23_5979041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_5979041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979041 prefixEnd_5979041 := by exact prefixLift 5979041
  have htrace : WordTrace (prefixWord ++ tailWord_5979041) baseStart_5979041 baseEnd_5979041 := by
    simpa [prefixWord, tailWord_5979041, baseEnd_5979041] using wordTrace_append hprefix tailTrace_5979041
  have hstable : (prefixWord ++ tailWord_5979041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979041).length < 2 ^ (prefixWord ++ tailWord_5979041).sum := by decide
  have hdescent : baseEnd_5979041 < baseStart_5979041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979077 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 7]
def baseStart_5979077 : Nat := 118140960795 + 5979077 * 2 ^ 59
def prefixEnd_5979077 : Nat := 4983230072969 + 3 ^ 40 * 5979077 * 2
def baseEnd_5979077 : Nat := 3070140371242608567440231

theorem tailTrace_5979077 : CollatzResearch.WordTrace tailWord_5979077 prefixEnd_5979077 3070140371242608567440231 := by
  unfold tailWord_5979077
  simp only [CollatzResearch.WordTrace]
  refine ⟨218074853759832648899199485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145383235839888432599466323 218074853759832648899199485)
  ·
    refine ⟨81778070159937243337199807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218074853759832648899199485 81778070159937243337199807)
    ·
      refine ⟨122667105239905865005799711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81778070159937243337199807 122667105239905865005799711)
      ·
        refine ⟨184000657859858797508699567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122667105239905865005799711 184000657859858797508699567)
        ·
          refine ⟨276000986789788196263049351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184000657859858797508699567 276000986789788196263049351)
          ·
            refine ⟨414001480184682294394574027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276000986789788196263049351 414001480184682294394574027)
            ·
              refine ⟨621002220277023441591861041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414001480184682294394574027 621002220277023441591861041)
              ·
                refine ⟨465751665207767581193895781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 621002220277023441591861041 465751665207767581193895781)
                ·
                  refine ⟨87328437226456421473855459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 465751665207767581193895781 87328437226456421473855459)
                  ·
                    refine ⟨130992655839684632210783189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87328437226456421473855459 130992655839684632210783189)
                    ·
                      refine ⟨3070140371242608567440231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130992655839684632210783189 3070140371242608567440231)
                      ·
                        rfl

theorem cell23_5979077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_5979077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979077 prefixEnd_5979077 := by exact prefixLift 5979077
  have htrace : WordTrace (prefixWord ++ tailWord_5979077) baseStart_5979077 baseEnd_5979077 := by
    simpa [prefixWord, tailWord_5979077, baseEnd_5979077] using wordTrace_append hprefix tailTrace_5979077
  have hstable : (prefixWord ++ tailWord_5979077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979077).length < 2 ^ (prefixWord ++ tailWord_5979077).sum := by decide
  have hdescent : baseEnd_5979077 < baseStart_5979077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979098 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3]
def baseStart_5979098 : Nat := 118140960795 + 5979098 * 2 ^ 59
def prefixEnd_5979098 : Nat := 4983230072969 + 3 ^ 40 * 5979098 * 2
def baseEnd_5979098 : Nat := 3070151154336352985277635

theorem tailTrace_5979098 : CollatzResearch.WordTrace tailWord_5979098 prefixEnd_5979098 3070151154336352985277635 := by
  unfold tailWord_5979098
  simp only [CollatzResearch.WordTrace]
  refine ⟨54518904923189142371428487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145383746461837712990475965 54518904923189142371428487)
  ·
    refine ⟨81778357384783713557142731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54518904923189142371428487 81778357384783713557142731)
    ·
      refine ⟨122667536077175570335714097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81778357384783713557142731 122667536077175570335714097)
      ·
        refine ⟨92000652057881677751785573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122667536077175570335714097 92000652057881677751785573)
        ·
          refine ⟨17250122260852814578459795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92000652057881677751785573 17250122260852814578459795)
          ·
            refine ⟨25875183391279221867689693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17250122260852814578459795 25875183391279221867689693)
            ·
              refine ⟨9703193771729708200383635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25875183391279221867689693 9703193771729708200383635)
              ·
                refine ⟨14554790657594562300575453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9703193771729708200383635 14554790657594562300575453)
                ·
                  refine ⟨5458046496597960862715795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14554790657594562300575453 5458046496597960862715795)
                  ·
                    refine ⟨8187069744896941294073693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5458046496597960862715795 8187069744896941294073693)
                    ·
                      refine ⟨3070151154336352985277635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8187069744896941294073693 3070151154336352985277635)
                      ·
                        rfl

theorem cell23_5979098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_5979098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979098 prefixEnd_5979098 := by exact prefixLift 5979098
  have htrace : WordTrace (prefixWord ++ tailWord_5979098) baseStart_5979098 baseEnd_5979098 := by
    simpa [prefixWord, tailWord_5979098, baseEnd_5979098] using wordTrace_append hprefix tailTrace_5979098
  have hstable : (prefixWord ++ tailWord_5979098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979098).length < 2 ^ (prefixWord ++ tailWord_5979098).sum := by decide
  have hdescent : baseEnd_5979098 < baseStart_5979098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979121 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 3, 1, 4]
def baseStart_5979121 : Nat := 118140960795 + 5979121 * 2 ^ 59
def prefixEnd_5979121 : Nat := 4983230072969 + 3 ^ 40 * 5979121 * 2
def baseEnd_5979121 : Nat := 3070162964391406395290029

theorem tailTrace_5979121 : CollatzResearch.WordTrace tailWord_5979121 prefixEnd_5979121 3070162964391406395290029 := by
  unfold tailWord_5979121
  simp only [CollatzResearch.WordTrace]
  refine ⟨218076458571673244413801217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145384305714448829609200811 218076458571673244413801217)
  ·
    refine ⟨163557343928754933310350913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218076458571673244413801217 163557343928754933310350913)
    ·
      refine ⟨122668007946566199982763185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163557343928754933310350913 122668007946566199982763185)
      ·
        refine ⟨92001005959924649987072389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122668007946566199982763185 92001005959924649987072389)
        ·
          refine ⟨17250188617485871872576073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92001005959924649987072389 17250188617485871872576073)
          ·
            refine ⟨12937641463114403904432055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17250188617485871872576073 12937641463114403904432055)
            ·
              refine ⟨19406462194671605856648083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12937641463114403904432055 19406462194671605856648083)
              ·
                refine ⟨29109693292007408784972125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19406462194671605856648083 29109693292007408784972125)
                ·
                  refine ⟨10916134984502778294364547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29109693292007408784972125 10916134984502778294364547)
                  ·
                    refine ⟨16374202476754167441546821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10916134984502778294364547 16374202476754167441546821)
                    ·
                      refine ⟨3070162964391406395290029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16374202476754167441546821 3070162964391406395290029)
                      ·
                        rfl

theorem cell23_5979121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_5979121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979121 prefixEnd_5979121 := by exact prefixLift 5979121
  have htrace : WordTrace (prefixWord ++ tailWord_5979121) baseStart_5979121 baseEnd_5979121 := by
    simpa [prefixWord, tailWord_5979121, baseEnd_5979121] using wordTrace_append hprefix tailTrace_5979121
  have hstable : (prefixWord ++ tailWord_5979121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979121).length < 2 ^ (prefixWord ++ tailWord_5979121).sum := by decide
  have hdescent : baseEnd_5979121 < baseStart_5979121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979148 : List Nat := [2, 2, 1, 2, 3, 3, 2, 2, 2, 4]
def baseStart_5979148 : Nat := 118140960795 + 5979148 * 2 ^ 59
def prefixEnd_5979148 : Nat := 4983230072969 + 3 ^ 40 * 5979148 * 2
def baseEnd_5979148 : Nat := 1023392276123025929884135

theorem tailTrace_5979148 : CollatzResearch.WordTrace tailWord_5979148 prefixEnd_5979148 1023392276123025929884135 := by
  unfold tailWord_5979148
  simp only [CollatzResearch.WordTrace]
  refine ⟨109038721671287714012517049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145384962228383618683356065 109038721671287714012517049)
  ·
    refine ⟨81779041253465785509387787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109038721671287714012517049 81779041253465785509387787)
    ·
      refine ⟨122668561880198678264081681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81779041253465785509387787 122668561880198678264081681)
      ·
        refine ⟨92001421410149008698061261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122668561880198678264081681 92001421410149008698061261)
        ·
          refine ⟨34500533028805878261772973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92001421410149008698061261 34500533028805878261772973)
          ·
            refine ⟨12937699885802204348164865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34500533028805878261772973 12937699885802204348164865)
            ·
              refine ⟨9703274914351653261123649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12937699885802204348164865 9703274914351653261123649)
              ·
                refine ⟨7277456185763739945842737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9703274914351653261123649 7277456185763739945842737)
                ·
                  refine ⟨5458092139322804959382053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7277456185763739945842737 5458092139322804959382053)
                  ·
                    refine ⟨1023392276123025929884135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5458092139322804959382053 1023392276123025929884135)
                    ·
                      rfl

theorem cell23_5979148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_5979148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979148 prefixEnd_5979148 := by exact prefixLift 5979148
  have htrace : WordTrace (prefixWord ++ tailWord_5979148) baseStart_5979148 baseEnd_5979148 := by
    simpa [prefixWord, tailWord_5979148, baseEnd_5979148] using wordTrace_append hprefix tailTrace_5979148
  have hstable : (prefixWord ++ tailWord_5979148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979148).length < 2 ^ (prefixWord ++ tailWord_5979148).sum := by decide
  have hdescent : baseEnd_5979148 < baseStart_5979148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979171 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 3]
def baseStart_5979171 : Nat := 118140960795 + 5979171 * 2 ^ 59
def prefixEnd_5979171 : Nat := 4983230072969 + 3 ^ 40 * 5979171 * 2
def baseEnd_5979171 : Nat := 3070188638424131199664799

theorem tailTrace_5979171 : CollatzResearch.WordTrace tailWord_5979171 prefixEnd_5979171 3070188638424131199664799 := by
  unfold tailWord_5979171
  simp only [CollatzResearch.WordTrace]
  refine ⟨218078282221492102953121367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145385521480994735302080911 218078282221492102953121367)
  ·
    refine ⟨327117423332238154429682051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218078282221492102953121367 327117423332238154429682051)
    ·
      refine ⟨490676134998357231644523077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327117423332238154429682051 490676134998357231644523077)
      ·
        refine ⟨92001775312191980933348077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 490676134998357231644523077 92001775312191980933348077)
        ·
          refine ⟨34500665742071992850005529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92001775312191980933348077 34500665742071992850005529)
          ·
            refine ⟨25875499306553994637504147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34500665742071992850005529 25875499306553994637504147)
            ·
              refine ⟨38813248959830991956256221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25875499306553994637504147 38813248959830991956256221)
              ·
                refine ⟨14554968359936621983596083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38813248959830991956256221 14554968359936621983596083)
                ·
                  refine ⟨21832452539904932975394125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14554968359936621983596083 21832452539904932975394125)
                  ·
                    refine ⟨8187169702464349865772797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21832452539904932975394125 8187169702464349865772797)
                    ·
                      refine ⟨3070188638424131199664799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8187169702464349865772797 3070188638424131199664799)
                      ·
                        rfl

theorem cell23_5979171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_5979171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979171 prefixEnd_5979171 := by exact prefixLift 5979171
  have htrace : WordTrace (prefixWord ++ tailWord_5979171) baseStart_5979171 baseEnd_5979171 := by
    simpa [prefixWord, tailWord_5979171, baseEnd_5979171] using wordTrace_append hprefix tailTrace_5979171
  have hstable : (prefixWord ++ tailWord_5979171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979171).length < 2 ^ (prefixWord ++ tailWord_5979171).sum := by decide
  have hdescent : baseEnd_5979171 < baseStart_5979171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979178 : List Nat := [3, 1, 4, 1, 3, 1, 3, 7]
def baseStart_5979178 : Nat := 118140960795 + 5979178 * 2 ^ 59
def prefixEnd_5979178 : Nat := 4983230072969 + 3 ^ 40 * 5979178 * 2
def baseEnd_5979178 : Nat := 113710823436618987862121

theorem tailTrace_5979178 : CollatzResearch.WordTrace tailWord_5979178 prefixEnd_5979178 113710823436618987862121 := by
  unfold tailWord_5979178
  simp only [CollatzResearch.WordTrace]
  refine ⟨54519634383116685787156547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145385691688311162099084125 54519634383116685787156547)
  ·
    refine ⟨81779451574675028680734821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54519634383116685787156547 81779451574675028680734821)
    ·
      refine ⟨15333647170251567877637779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81779451574675028680734821 15333647170251567877637779)
      ·
        refine ⟨23000470755377351816456669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15333647170251567877637779 23000470755377351816456669)
        ·
          refine ⟨8625176533266506931171251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23000470755377351816456669 8625176533266506931171251)
          ·
            refine ⟨12937764799899760396756877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8625176533266506931171251 12937764799899760396756877)
            ·
              refine ⟨4851661799962410148783829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12937764799899760396756877 4851661799962410148783829)
              ·
                refine ⟨113710823436618987862121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4851661799962410148783829 113710823436618987862121)
                ·
                  rfl

theorem cell23_5979178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 7].length) (baseStart_5979178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979178 prefixEnd_5979178 := by exact prefixLift 5979178
  have htrace : WordTrace (prefixWord ++ tailWord_5979178) baseStart_5979178 baseEnd_5979178 := by
    simpa [prefixWord, tailWord_5979178, baseEnd_5979178] using wordTrace_append hprefix tailTrace_5979178
  have hstable : (prefixWord ++ tailWord_5979178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979178).length < 2 ^ (prefixWord ++ tailWord_5979178).sum := by decide
  have hdescent : baseEnd_5979178 < baseStart_5979178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979184 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 5]
def baseStart_5979184 : Nat := 118140960795 + 5979184 * 2 ^ 59
def prefixEnd_5979184 : Nat := 4983230072969 + 3 ^ 40 * 5979184 * 2
def baseEnd_5979184 : Nat := 3070195313672639648802239

theorem tailTrace_5979184 : CollatzResearch.WordTrace tailWord_5979184 prefixEnd_5979184 3070195313672639648802239 := by
  unfold tailWord_5979184
  simp only [CollatzResearch.WordTrace]
  refine ⟨109039378185222503086672303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145385837580296670782229737 109039378185222503086672303)
  ·
    refine ⟨163559067277833754630008455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109039378185222503086672303 163559067277833754630008455)
    ·
      refine ⟨245338600916750631945012683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163559067277833754630008455 245338600916750631945012683)
      ·
        refine ⟨368007901375125947917519025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245338600916750631945012683 368007901375125947917519025)
        ·
          refine ⟨276005926031344460938139269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368007901375125947917519025 276005926031344460938139269)
          ·
            refine ⟨51751111130877086425901113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 276005926031344460938139269 51751111130877086425901113)
            ·
              refine ⟨38813333348157814819425835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51751111130877086425901113 38813333348157814819425835)
              ·
                refine ⟨58220000022236722229138753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38813333348157814819425835 58220000022236722229138753)
                ·
                  refine ⟨43665000016677541671854065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58220000022236722229138753 43665000016677541671854065)
                  ·
                    refine ⟨32748750012508156253890549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43665000016677541671854065 32748750012508156253890549)
                    ·
                      refine ⟨3070195313672639648802239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32748750012508156253890549 3070195313672639648802239)
                      ·
                        rfl

theorem cell23_5979184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_5979184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979184 prefixEnd_5979184 := by exact prefixLift 5979184
  have htrace : WordTrace (prefixWord ++ tailWord_5979184) baseStart_5979184 baseEnd_5979184 := by
    simpa [prefixWord, tailWord_5979184, baseEnd_5979184] using wordTrace_append hprefix tailTrace_5979184
  have hstable : (prefixWord ++ tailWord_5979184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979184).length < 2 ^ (prefixWord ++ tailWord_5979184).sum := by decide
  have hdescent : baseEnd_5979184 < baseStart_5979184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979245 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 4, 2, 2]
def baseStart_5979245 : Nat := 118140960795 + 5979245 * 2 ^ 59
def prefixEnd_5979245 : Nat := 4983230072969 + 3 ^ 40 * 5979245 * 2
def baseEnd_5979245 : Nat := 3070226635992563910139459

theorem tailTrace_5979245 : CollatzResearch.WordTrace tailWord_5979245 prefixEnd_5979245 3070226635992563910139459 := by
  unfold tailWord_5979245
  simp only [CollatzResearch.WordTrace]
  refine ⟨218080981223224013591315189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145387320815482675727543459 218080981223224013591315189)
  ·
    refine ⟨20445091989677251274185799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218080981223224013591315189 20445091989677251274185799)
    ·
      refine ⟨30667637984515876911278699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20445091989677251274185799 30667637984515876911278699)
      ·
        refine ⟨46001456976773815366918049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30667637984515876911278699 46001456976773815366918049)
        ·
          refine ⟨34501092732580361525188537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46001456976773815366918049 34501092732580361525188537)
          ·
            refine ⟨25875819549435271143891403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34501092732580361525188537 25875819549435271143891403)
            ·
              refine ⟨38813729324152906715837105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25875819549435271143891403 38813729324152906715837105)
              ·
                refine ⟨29110296993114680036877829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38813729324152906715837105 29110296993114680036877829)
                ·
                  refine ⟨5458180686209002506914593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29110296993114680036877829 5458180686209002506914593)
                  ·
                    refine ⟨4093635514656751880185945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5458180686209002506914593 4093635514656751880185945)
                    ·
                      refine ⟨3070226635992563910139459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4093635514656751880185945 3070226635992563910139459)
                      ·
                        rfl

theorem cell23_5979245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_5979245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979245 prefixEnd_5979245 := by exact prefixLift 5979245
  have htrace : WordTrace (prefixWord ++ tailWord_5979245) baseStart_5979245 baseEnd_5979245 := by
    simpa [prefixWord, tailWord_5979245, baseEnd_5979245] using wordTrace_append hprefix tailTrace_5979245
  have hstable : (prefixWord ++ tailWord_5979245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979245).length < 2 ^ (prefixWord ++ tailWord_5979245).sum := by decide
  have hdescent : baseEnd_5979245 < baseStart_5979245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979268 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 7]
def baseStart_5979268 : Nat := 118140960795 + 5979268 * 2 ^ 59
def prefixEnd_5979268 : Nat := 4983230072969 + 3 ^ 40 * 5979268 * 2
def baseEnd_5979268 : Nat := 341137605116401924461317

theorem tailTrace_5979268 : CollatzResearch.WordTrace tailWord_5979268 prefixEnd_5979268 341137605116401924461317 := by
  unfold tailWord_5979268
  simp only [CollatzResearch.WordTrace]
  refine ⟨109040910051070344259701229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145387880068093792346268305 109040910051070344259701229)
  ·
    refine ⟨40890341269151379097387961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109040910051070344259701229 40890341269151379097387961)
    ·
      refine ⟨30667755951863534323040971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40890341269151379097387961 30667755951863534323040971)
      ·
        refine ⟨46001633927795301484561457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30667755951863534323040971 46001633927795301484561457)
        ·
          refine ⟨34501225445846476113421093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46001633927795301484561457 34501225445846476113421093)
          ·
            refine ⟨6468979771096214271266455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34501225445846476113421093 6468979771096214271266455)
            ·
              refine ⟨9703469656644321406899683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6468979771096214271266455 9703469656644321406899683)
              ·
                refine ⟨14555204484966482110349525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9703469656644321406899683 14555204484966482110349525)
                ·
                  refine ⟨341137605116401924461317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14555204484966482110349525 341137605116401924461317)
                  ·
                    rfl

theorem cell23_5979268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_5979268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979268 prefixEnd_5979268 := by exact prefixLift 5979268
  have htrace : WordTrace (prefixWord ++ tailWord_5979268) baseStart_5979268 baseEnd_5979268 := by
    simpa [prefixWord, tailWord_5979268, baseEnd_5979268] using wordTrace_append hprefix tailTrace_5979268
  have hstable : (prefixWord ++ tailWord_5979268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979268).length < 2 ^ (prefixWord ++ tailWord_5979268).sum := by decide
  have hdescent : baseEnd_5979268 < baseStart_5979268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979352 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 2, 1, 4]
def baseStart_5979352 : Nat := 118140960795 + 5979352 * 2 ^ 59
def prefixEnd_5979352 : Nat := 4983230072969 + 3 ^ 40 * 5979352 * 2
def baseEnd_5979352 : Nat := 3070281578422594991501467

theorem tailTrace_5979352 : CollatzResearch.WordTrace tailWord_5979352 prefixEnd_5979352 3070281578422594991501467 := by
  unfold tailWord_5979352
  simp only [CollatzResearch.WordTrace]
  refine ⟨109042441916918185432730155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145389922555890913910306873 109042441916918185432730155)
  ·
    refine ⟨163563662875377278149095233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109042441916918185432730155 163563662875377278149095233)
    ·
      refine ⟨122672747156532958611821425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163563662875377278149095233 122672747156532958611821425)
      ·
        refine ⟨92004560367399718958866069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122672747156532958611821425 92004560367399718958866069)
        ·
          refine ⟨4312713767221861826196847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 92004560367399718958866069 4312713767221861826196847)
          ·
            refine ⟨6469070650832792739295271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4312713767221861826196847 6469070650832792739295271)
            ·
              refine ⟨9703605976249189108942907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6469070650832792739295271 9703605976249189108942907)
              ·
                refine ⟨14555408964373783663414361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9703605976249189108942907 14555408964373783663414361)
                ·
                  refine ⟨10916556723280337747560771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14555408964373783663414361 10916556723280337747560771)
                  ·
                    refine ⟨16374835084920506621341157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10916556723280337747560771 16374835084920506621341157)
                    ·
                      refine ⟨3070281578422594991501467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16374835084920506621341157 3070281578422594991501467)
                      ·
                        rfl

theorem cell23_5979352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_5979352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979352 prefixEnd_5979352 := by exact prefixLift 5979352
  have htrace : WordTrace (prefixWord ++ tailWord_5979352) baseStart_5979352 baseEnd_5979352 := by
    simpa [prefixWord, tailWord_5979352, baseEnd_5979352] using wordTrace_append hprefix tailTrace_5979352
  have hstable : (prefixWord ++ tailWord_5979352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979352).length < 2 ^ (prefixWord ++ tailWord_5979352).sum := by decide
  have hdescent : baseEnd_5979352 < baseStart_5979352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979375 : List Nat := [1, 1, 2, 1, 7, 2, 1, 2, 6]
def baseStart_5979375 : Nat := 118140960795 + 5979375 * 2 ^ 59
def prefixEnd_5979375 : Nat := 4983230072969 + 3 ^ 40 * 5979375 * 2
def baseEnd_5979375 : Nat := 341143709830849822390429

theorem tailTrace_5979375 : CollatzResearch.WordTrace tailWord_5979375 prefixEnd_5979375 341143709830849822390429 := by
  unfold tailWord_5979375
  simp only [CollatzResearch.WordTrace]
  refine ⟨218085722712753045793547579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145390481808502030529031719 218085722712753045793547579)
  ·
    refine ⟨327128584069129568690321369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218085722712753045793547579 327128584069129568690321369)
    ·
      refine ⟨245346438051847176517741027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327128584069129568690321369 245346438051847176517741027)
      ·
        refine ⟨368019657077770764776611541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245346438051847176517741027 368019657077770764776611541)
        ·
          refine ⟨8625460712760252299451833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 368019657077770764776611541 8625460712760252299451833)
          ·
            refine ⟨6469095534570189224588875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8625460712760252299451833 6469095534570189224588875)
            ·
              refine ⟨9703643301855283836883313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6469095534570189224588875 9703643301855283836883313)
              ·
                refine ⟨7277732476391462877662485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9703643301855283836883313 7277732476391462877662485)
                ·
                  refine ⟨341143709830849822390429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7277732476391462877662485 341143709830849822390429)
                  ·
                    rfl

theorem cell23_5979375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 6].length) (baseStart_5979375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979375 prefixEnd_5979375 := by exact prefixLift 5979375
  have htrace : WordTrace (prefixWord ++ tailWord_5979375) baseStart_5979375 baseEnd_5979375 := by
    simpa [prefixWord, tailWord_5979375, baseEnd_5979375] using wordTrace_append hprefix tailTrace_5979375
  have hstable : (prefixWord ++ tailWord_5979375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979375).length < 2 ^ (prefixWord ++ tailWord_5979375).sum := by decide
  have hdescent : baseEnd_5979375 < baseStart_5979375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979385 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 3, 1, 3]
def baseStart_5979385 : Nat := 118140960795 + 5979385 * 2 ^ 59
def prefixEnd_5979385 : Nat := 4983230072969 + 3 ^ 40 * 5979385 * 2
def baseEnd_5979385 : Nat := 3070298523284193362388815

theorem tailTrace_5979385 : CollatzResearch.WordTrace tailWord_5979385 prefixEnd_5979385 3070298523284193362388815 := by
  unfold tailWord_5979385
  simp only [CollatzResearch.WordTrace]
  refine ⟨218086087442716817501411609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145390724961811211667607739 218086087442716817501411609)
  ·
    refine ⟨163564565582037613126058707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218086087442716817501411609 163564565582037613126058707)
    ·
      refine ⟨245346848373056419689088061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163564565582037613126058707 245346848373056419689088061)
      ·
        refine ⟨92005068139896157383408023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245346848373056419689088061 92005068139896157383408023)
        ·
          refine ⟨138007602209844236075112035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92005068139896157383408023 138007602209844236075112035)
          ·
            refine ⟨207011403314766354112668053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138007602209844236075112035 207011403314766354112668053)
            ·
              refine ⟨9703659530379672849031315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 207011403314766354112668053 9703659530379672849031315)
              ·
                refine ⟨14555489295569509273546973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9703659530379672849031315 14555489295569509273546973)
                ·
                  refine ⟨5458308485838565977580115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14555489295569509273546973 5458308485838565977580115)
                  ·
                    refine ⟨8187462728757848966370173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5458308485838565977580115 8187462728757848966370173)
                    ·
                      refine ⟨3070298523284193362388815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8187462728757848966370173 3070298523284193362388815)
                      ·
                        rfl

theorem cell23_5979385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_5979385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979385 prefixEnd_5979385 := by exact prefixLift 5979385
  have htrace : WordTrace (prefixWord ++ tailWord_5979385) baseStart_5979385 baseEnd_5979385 := by
    simpa [prefixWord, tailWord_5979385, baseEnd_5979385] using wordTrace_append hprefix tailTrace_5979385
  have hstable : (prefixWord ++ tailWord_5979385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979385).length < 2 ^ (prefixWord ++ tailWord_5979385).sum := by decide
  have hdescent : baseEnd_5979385 < baseStart_5979385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979452 : List Nat := [2, 2, 2, 2, 1, 3, 4, 1, 2, 4]
def baseStart_5979452 : Nat := 118140960795 + 5979452 * 2 ^ 59
def prefixEnd_5979452 : Nat := 4983230072969 + 3 ^ 40 * 5979452 * 2
def baseEnd_5979452 : Nat := 1023444308829348200083669

theorem tailTrace_5979452 : CollatzResearch.WordTrace tailWord_5979452 prefixEnd_5979452 1023444308829348200083669 := by
  unfold tailWord_5979452
  simp only [CollatzResearch.WordTrace]
  refine ⟨109044265566737043972050305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145392354088982725296067073 109044265566737043972050305)
  ·
    refine ⟨81783199175052782979037729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109044265566737043972050305 81783199175052782979037729)
    ·
      refine ⟨61337399381289587234278297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81783199175052782979037729 61337399381289587234278297)
      ·
        refine ⟨46003049535967190425708723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61337399381289587234278297 46003049535967190425708723)
        ·
          refine ⟨69004574303950785638563085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46003049535967190425708723 69004574303950785638563085)
          ·
            refine ⟨25876715363981544614461157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69004574303950785638563085 25876715363981544614461157)
            ·
              refine ⟨4851884130746539615211467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25876715363981544614461157 4851884130746539615211467)
              ·
                refine ⟨7277826196119809422817201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4851884130746539615211467 7277826196119809422817201)
                ·
                  refine ⟨5458369647089857067112901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7277826196119809422817201 5458369647089857067112901)
                  ·
                    refine ⟨1023444308829348200083669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5458369647089857067112901 1023444308829348200083669)
                    ·
                      rfl

theorem cell23_5979452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_5979452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979452 prefixEnd_5979452 := by exact prefixLift 5979452
  have htrace : WordTrace (prefixWord ++ tailWord_5979452) baseStart_5979452 baseEnd_5979452 := by
    simpa [prefixWord, tailWord_5979452, baseEnd_5979452] using wordTrace_append hprefix tailTrace_5979452
  have hstable : (prefixWord ++ tailWord_5979452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979452).length < 2 ^ (prefixWord ++ tailWord_5979452).sum := by decide
  have hdescent : baseEnd_5979452 < baseStart_5979452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979471 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 7]
def baseStart_5979471 : Nat := 118140960795 + 5979471 * 2 ^ 59
def prefixEnd_5979471 : Nat := 4983230072969 + 3 ^ 40 * 5979471 * 2
def baseEnd_5979471 : Nat := 3070342682620480025913419

theorem tailTrace_5979471 : CollatzResearch.WordTrace tailWord_5979471 prefixEnd_5979471 3070342682620480025913419 := by
  unfold tailWord_5979471
  simp only [CollatzResearch.WordTrace]
  refine ⟨218089224120405254189042267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145392816080270169459361511 218089224120405254189042267)
  ·
    refine ⟨327133836180607881283563401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218089224120405254189042267 327133836180607881283563401)
    ·
      refine ⟨245350377135455910962672551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327133836180607881283563401 245350377135455910962672551)
      ·
        refine ⟨368025565703183866444008827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245350377135455910962672551 368025565703183866444008827)
        ·
          refine ⟨552038348554775799666013241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368025565703183866444008827 552038348554775799666013241)
          ·
            refine ⟨414028761416081849749509931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552038348554775799666013241 414028761416081849749509931)
            ·
              refine ⟨621043142124122774624264897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414028761416081849749509931 621043142124122774624264897)
              ·
                refine ⟨465782356593092080968198673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 621043142124122774624264897 465782356593092080968198673)
                ·
                  refine ⟨349336767444819060726149005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465782356593092080968198673 349336767444819060726149005)
                  ·
                    refine ⟨131001287791807147772305877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 349336767444819060726149005 131001287791807147772305877)
                    ·
                      refine ⟨3070342682620480025913419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131001287791807147772305877 3070342682620480025913419)
                      ·
                        rfl

theorem cell23_5979471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_5979471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979471 prefixEnd_5979471 := by exact prefixLift 5979471
  have htrace : WordTrace (prefixWord ++ tailWord_5979471) baseStart_5979471 baseEnd_5979471 := by
    simpa [prefixWord, tailWord_5979471, baseEnd_5979471] using wordTrace_append hprefix tailTrace_5979471
  have hstable : (prefixWord ++ tailWord_5979471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979471).length < 2 ^ (prefixWord ++ tailWord_5979471).sum := by decide
  have hdescent : baseEnd_5979471 < baseStart_5979471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979492 : List Nat := [2, 3, 1, 1, 3, 2, 1, 4, 2, 1, 3]
def baseStart_5979492 : Nat := 118140960795 + 5979492 * 2 ^ 59
def prefixEnd_5979492 : Nat := 4983230072969 + 3 ^ 40 * 5979492 * 2
def baseEnd_5979492 : Nat := 3070353465714224443750823

theorem tailTrace_5979492 : CollatzResearch.WordTrace tailWord_5979492 prefixEnd_5979492 3070353465714224443750823 := by
  unfold tailWord_5979492
  simp only [CollatzResearch.WordTrace]
  refine ⟨109044995026664587387778365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145393326702219449850371153 109044995026664587387778365)
  ·
    refine ⟨40891873134999220270416887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109044995026664587387778365 40891873134999220270416887)
    ·
      refine ⟨61337809702498830405625331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40891873134999220270416887 61337809702498830405625331)
      ·
        refine ⟨92006714553748245608437997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61337809702498830405625331 92006714553748245608437997)
        ·
          refine ⟨34502517957655592103164249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92006714553748245608437997 34502517957655592103164249)
          ·
            refine ⟨25876888468241694077373187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34502517957655592103164249 25876888468241694077373187)
            ·
              refine ⟨38815332702362541116059781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25876888468241694077373187 38815332702362541116059781)
              ·
                refine ⟨7277874881692976459261209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38815332702362541116059781 7277874881692976459261209)
                ·
                  refine ⟨5458406161269732344445907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7277874881692976459261209 5458406161269732344445907)
                  ·
                    refine ⟨8187609241904598516668861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5458406161269732344445907 8187609241904598516668861)
                    ·
                      refine ⟨3070353465714224443750823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8187609241904598516668861 3070353465714224443750823)
                      ·
                        rfl

theorem cell23_5979492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_5979492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979492 prefixEnd_5979492 := by exact prefixLift 5979492
  have htrace : WordTrace (prefixWord ++ tailWord_5979492) baseStart_5979492 baseEnd_5979492 := by
    simpa [prefixWord, tailWord_5979492, baseEnd_5979492] using wordTrace_append hprefix tailTrace_5979492
  have hstable : (prefixWord ++ tailWord_5979492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979492).length < 2 ^ (prefixWord ++ tailWord_5979492).sum := by decide
  have hdescent : baseEnd_5979492 < baseStart_5979492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979532 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 4, 2, 2]
def baseStart_5979532 : Nat := 118140960795 + 5979532 * 2 ^ 59
def prefixEnd_5979532 : Nat := 4983230072969 + 3 ^ 40 * 5979532 * 2
def baseEnd_5979532 : Nat := 3070374004940404287250639

theorem tailTrace_5979532 : CollatzResearch.WordTrace tailWord_5979532 prefixEnd_5979532 3070374004940404287250639 := by
  unfold tailWord_5979532
  simp only [CollatzResearch.WordTrace]
  refine ⟨109045724486592130803506425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145394299315456174404675233 109045724486592130803506425)
  ·
    refine ⟨81784293364944098102629819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109045724486592130803506425 81784293364944098102629819)
    ·
      refine ⟨122676440047416147153944729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81784293364944098102629819 122676440047416147153944729)
      ·
        refine ⟨92007330035562110365458547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122676440047416147153944729 92007330035562110365458547)
        ·
          refine ⟨138010995053343165548187821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92007330035562110365458547 138010995053343165548187821)
          ·
            refine ⟨51754123145003687080570433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138010995053343165548187821 51754123145003687080570433)
            ·
              refine ⟨38815592358752765310427825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51754123145003687080570433 38815592358752765310427825)
              ·
                refine ⟨29111694269064573982820869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38815592358752765310427825 29111694269064573982820869)
                ·
                  refine ⟨5458442675449607621778913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29111694269064573982820869 5458442675449607621778913)
                  ·
                    refine ⟨4093832006587205716334185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5458442675449607621778913 4093832006587205716334185)
                    ·
                      refine ⟨3070374004940404287250639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4093832006587205716334185 3070374004940404287250639)
                      ·
                        rfl

theorem cell23_5979532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_5979532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979532 prefixEnd_5979532 := by exact prefixLift 5979532
  have htrace : WordTrace (prefixWord ++ tailWord_5979532) baseStart_5979532 baseEnd_5979532 := by
    simpa [prefixWord, tailWord_5979532, baseEnd_5979532] using wordTrace_append hprefix tailTrace_5979532
  have hstable : (prefixWord ++ tailWord_5979532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979532).length < 2 ^ (prefixWord ++ tailWord_5979532).sum := by decide
  have hdescent : baseEnd_5979532 < baseStart_5979532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979549 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 4, 2, 2]
def baseStart_5979549 : Nat := 118140960795 + 5979549 * 2 ^ 59
def prefixEnd_5979549 : Nat := 4983230072969 + 3 ^ 40 * 5979549 * 2
def baseEnd_5979549 : Nat := 3070382734111530720738061

theorem tailTrace_5979549 : CollatzResearch.WordTrace tailWord_5979549 prefixEnd_5979549 3070382734111530720738061 := by
  unfold tailWord_5979549
  simp only [CollatzResearch.WordTrace]
  refine ⟨218092069014122673510381701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145394712676081782340254467 218092069014122673510381701)
  ·
    refine ⟨40892262940148001283196569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218092069014122673510381701 40892262940148001283196569)
    ·
      refine ⟨30669197205111000962397427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40892262940148001283196569 30669197205111000962397427)
      ·
        refine ⟨46003795807666501443596141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30669197205111000962397427 46003795807666501443596141)
        ·
          refine ⟨17251423427874938041348553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46003795807666501443596141 17251423427874938041348553)
          ·
            refine ⟨12938567570906203531011415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17251423427874938041348553 12938567570906203531011415)
            ·
              refine ⟨19407851356359305296517123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12938567570906203531011415 19407851356359305296517123)
              ·
                refine ⟨29111777034538957944775685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19407851356359305296517123 29111777034538957944775685)
                ·
                  refine ⟨5458458193976054614645441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29111777034538957944775685 5458458193976054614645441)
                  ·
                    refine ⟨4093843645482040960984081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5458458193976054614645441 4093843645482040960984081)
                    ·
                      refine ⟨3070382734111530720738061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4093843645482040960984081 3070382734111530720738061)
                      ·
                        rfl

theorem cell23_5979549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_5979549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979549 prefixEnd_5979549 := by exact prefixLift 5979549
  have htrace : WordTrace (prefixWord ++ tailWord_5979549) baseStart_5979549 baseEnd_5979549 := by
    simpa [prefixWord, tailWord_5979549, baseEnd_5979549] using wordTrace_append hprefix tailTrace_5979549
  have hstable : (prefixWord ++ tailWord_5979549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979549).length < 2 ^ (prefixWord ++ tailWord_5979549).sum := by decide
  have hdescent : baseEnd_5979549 < baseStart_5979549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979555 : List Nat := [1, 1, 1, 4, 1, 3, 1, 6, 5]
def baseStart_5979555 : Nat := 118140960795 + 5979555 * 2 ^ 59
def prefixEnd_5979555 : Nat := 4983230072969 + 3 ^ 40 * 5979555 * 2
def baseEnd_5979555 : Nat := 341153979443939744140337

theorem tailTrace_5979555 : CollatzResearch.WordTrace tailWord_5979555 prefixEnd_5979555 341153979443939744140337 := by
  unfold tailWord_5979555
  simp only [CollatzResearch.WordTrace]
  refine ⟨218092287852100936535100119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145394858568067291023400079 218092287852100936535100119)
  ·
    refine ⟨327138431778151404802650179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218092287852100936535100119 327138431778151404802650179)
    ·
      refine ⟨490707647667227107203975269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327138431778151404802650179 490707647667227107203975269)
      ·
        refine ⟨92007683937605082600745363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 490707647667227107203975269 92007683937605082600745363)
        ·
          refine ⟨138011525906407623901118045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92007683937605082600745363 138011525906407623901118045)
          ·
            refine ⟨51754322214902858962919267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138011525906407623901118045 51754322214902858962919267)
            ·
              refine ⟨77631483322354288444378901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51754322214902858962919267 77631483322354288444378901)
              ·
                refine ⟨3638975780735357270830261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77631483322354288444378901 3638975780735357270830261)
                ·
                  refine ⟨341153979443939744140337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3638975780735357270830261 341153979443939744140337)
                  ·
                    rfl

theorem cell23_5979555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 5].length) (baseStart_5979555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979555 prefixEnd_5979555 := by exact prefixLift 5979555
  have htrace : WordTrace (prefixWord ++ tailWord_5979555) baseStart_5979555 baseEnd_5979555 := by
    simpa [prefixWord, tailWord_5979555, baseEnd_5979555] using wordTrace_append hprefix tailTrace_5979555
  have hstable : (prefixWord ++ tailWord_5979555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979555).length < 2 ^ (prefixWord ++ tailWord_5979555).sum := by decide
  have hdescent : baseEnd_5979555 < baseStart_5979555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979568 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 6, 5]
def baseStart_5979568 : Nat := 118140960795 + 5979568 * 2 ^ 59
def prefixEnd_5979568 : Nat := 4983230072969 + 3 ^ 40 * 5979568 * 2
def baseEnd_5979568 : Nat := 1023464163414655382133491

theorem tailTrace_5979568 : CollatzResearch.WordTrace tailWord_5979568 prefixEnd_5979568 1023464163414655382133491 := by
  unfold tailWord_5979568
  simp only [CollatzResearch.WordTrace]
  refine ⟨109046381000526919877661679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145395174667369226503548905 109046381000526919877661679)
  ·
    refine ⟨163569571500790379816492519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109046381000526919877661679 163569571500790379816492519)
    ·
      refine ⟨245354357251185569724738779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163569571500790379816492519 245354357251185569724738779)
      ·
        refine ⟨368031535876778354587108169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245354357251185569724738779 368031535876778354587108169)
        ·
          refine ⟨276023651907583765940331127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368031535876778354587108169 276023651907583765940331127)
          ·
            refine ⟨414035477861375648910496691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276023651907583765940331127 414035477861375648910496691)
            ·
              refine ⟨621053216792063473365745037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414035477861375648910496691 621053216792063473365745037)
              ·
                refine ⟨232894956297023802512154389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 621053216792063473365745037 232894956297023802512154389)
                ·
                  refine ⟨10916951076422990742757237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 232894956297023802512154389 10916951076422990742757237)
                  ·
                    refine ⟨1023464163414655382133491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10916951076422990742757237 1023464163414655382133491)
                    ·
                      rfl

theorem cell23_5979568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 6, 5].length) (baseStart_5979568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979568 prefixEnd_5979568 := by exact prefixLift 5979568
  have htrace : WordTrace (prefixWord ++ tailWord_5979568) baseStart_5979568 baseEnd_5979568 := by
    simpa [prefixWord, tailWord_5979568, baseEnd_5979568] using wordTrace_append hprefix tailTrace_5979568
  have hstable : (prefixWord ++ tailWord_5979568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979568).length < 2 ^ (prefixWord ++ tailWord_5979568).sum := by decide
  have hdescent : baseEnd_5979568 < baseStart_5979568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979578 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5]
def baseStart_5979578 : Nat := 118140960795 + 5979578 * 2 ^ 59
def prefixEnd_5979578 : Nat := 4983230072969 + 3 ^ 40 * 5979578 * 2
def baseEnd_5979578 : Nat := 3070397625050511107275427

theorem tailTrace_5979578 : CollatzResearch.WordTrace tailWord_5979578 prefixEnd_5979578 3070397625050511107275427 := by
  unfold tailWord_5979578
  simp only [CollatzResearch.WordTrace]
  refine ⟨54523281682754402865796847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145395417820678407642124925 54523281682754402865796847)
  ·
    refine ⟨81784922524131604298695271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54523281682754402865796847 81784922524131604298695271)
    ·
      refine ⟨122677383786197406448042907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81784922524131604298695271 122677383786197406448042907)
      ·
        refine ⟨184016075679296109672064361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122677383786197406448042907 184016075679296109672064361)
        ·
          refine ⟨138012056759472082254048271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184016075679296109672064361 138012056759472082254048271)
          ·
            refine ⟨207018085139208123381072407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138012056759472082254048271 207018085139208123381072407)
            ·
              refine ⟨310527127708812185071608611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207018085139208123381072407 310527127708812185071608611)
              ·
                refine ⟨465790691563218277607412917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310527127708812185071608611 465790691563218277607412917)
                ·
                  refine ⟨43667877334051713525694961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 465790691563218277607412917 43667877334051713525694961)
                  ·
                    refine ⟨32750908000538785144271221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43667877334051713525694961 32750908000538785144271221)
                    ·
                      refine ⟨3070397625050511107275427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32750908000538785144271221 3070397625050511107275427)
                      ·
                        rfl

theorem cell23_5979578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_5979578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979578 prefixEnd_5979578 := by exact prefixLift 5979578
  have htrace : WordTrace (prefixWord ++ tailWord_5979578) baseStart_5979578 baseEnd_5979578 := by
    simpa [prefixWord, tailWord_5979578, baseEnd_5979578] using wordTrace_append hprefix tailTrace_5979578
  have hstable : (prefixWord ++ tailWord_5979578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979578).length < 2 ^ (prefixWord ++ tailWord_5979578).sum := by decide
  have hdescent : baseEnd_5979578 < baseStart_5979578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979606 : List Nat := [5, 2, 1, 1, 1, 3, 3, 2, 5]
def baseStart_5979606 : Nat := 118140960795 + 5979606 * 2 ^ 59
def prefixEnd_5979606 : Nat := 4983230072969 + 3 ^ 40 * 5979606 * 2
def baseEnd_5979606 : Nat := 341156889167648555302811

theorem tailTrace_5979606 : CollatzResearch.WordTrace tailWord_5979606 prefixEnd_5979606 341156889167648555302811 := by
  unfold tailWord_5979606
  simp only [CollatzResearch.WordTrace]
  refine ⟨13630884248432260765325417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145396098649944114830137781 13630884248432260765325417)
  ·
    refine ⟨10223163186324195573994063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13630884248432260765325417 10223163186324195573994063)
    ·
      refine ⟨15334744779486293360991095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10223163186324195573994063 15334744779486293360991095)
      ·
        refine ⟨23002117169229440041486643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15334744779486293360991095 23002117169229440041486643)
        ·
          refine ⟨34503175753844160062229965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23002117169229440041486643 34503175753844160062229965)
          ·
            refine ⟨12938690907691560023336237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34503175753844160062229965 12938690907691560023336237)
            ·
              refine ⟨4852009090384335008751089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12938690907691560023336237 4852009090384335008751089)
              ·
                refine ⟨3639006817788251256563317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4852009090384335008751089 3639006817788251256563317)
                ·
                  refine ⟨341156889167648555302811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3639006817788251256563317 341156889167648555302811)
                  ·
                    rfl

theorem cell23_5979606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_5979606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979606 prefixEnd_5979606 := by exact prefixLift 5979606
  have htrace : WordTrace (prefixWord ++ tailWord_5979606) baseStart_5979606 baseEnd_5979606 := by
    simpa [prefixWord, tailWord_5979606, baseEnd_5979606] using wordTrace_append hprefix tailTrace_5979606
  have hstable : (prefixWord ++ tailWord_5979606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979606).length < 2 ^ (prefixWord ++ tailWord_5979606).sum := by decide
  have hdescent : baseEnd_5979606 < baseStart_5979606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979628 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 10]
def baseStart_5979628 : Nat := 118140960795 + 5979628 * 2 ^ 59
def prefixEnd_5979628 : Nat := 4983230072969 + 3 ^ 40 * 5979628 * 2
def baseEnd_5979628 : Nat := 341158144342581767961133

theorem tailTrace_5979628 : CollatzResearch.WordTrace tailWord_5979628 prefixEnd_5979628 341158144342581767961133 := by
  unfold tailWord_5979628
  simp only [CollatzResearch.WordTrace]
  refine ⟨109047475190418235001253769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145396633587224313335005025 109047475190418235001253769)
  ·
    refine ⟨81785606392813676250940327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109047475190418235001253769 81785606392813676250940327)
    ·
      refine ⟨122678409589220514376410491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81785606392813676250940327 122678409589220514376410491)
      ·
        refine ⟨184017614383830771564615737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122678409589220514376410491 184017614383830771564615737)
        ·
          refine ⟨138013210787873078673461803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184017614383830771564615737 138013210787873078673461803)
          ·
            refine ⟨207019816181809618010192705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138013210787873078673461803 207019816181809618010192705)
            ·
              refine ⟨155264862136357213507644529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207019816181809618010192705 155264862136357213507644529)
              ·
                refine ⟨116448646602267910130733397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155264862136357213507644529 116448646602267910130733397)
                ·
                  refine ⟨341158144342581767961133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 116448646602267910130733397 341158144342581767961133)
                  ·
                    rfl

theorem cell23_5979628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 10].length) (baseStart_5979628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979628 prefixEnd_5979628 := by exact prefixLift 5979628
  have htrace : WordTrace (prefixWord ++ tailWord_5979628) baseStart_5979628 baseEnd_5979628 := by
    simpa [prefixWord, tailWord_5979628, baseEnd_5979628] using wordTrace_append hprefix tailTrace_5979628
  have hstable : (prefixWord ++ tailWord_5979628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979628).length < 2 ^ (prefixWord ++ tailWord_5979628).sum := by decide
  have hdescent : baseEnd_5979628 < baseStart_5979628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979642 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3]
def baseStart_5979642 : Nat := 118140960795 + 5979642 * 2 ^ 59
def prefixEnd_5979642 : Nat := 4983230072969 + 3 ^ 40 * 5979642 * 2
def baseEnd_5979642 : Nat := 3070430487812398856875133

theorem tailTrace_5979642 : CollatzResearch.WordTrace tailWord_5979642 prefixEnd_5979642 3070430487812398856875133 := by
  unfold tailWord_5979642
  simp only [CollatzResearch.WordTrace]
  refine ⟨54523865250696437598379295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145396974001857166929011453 54523865250696437598379295)
  ·
    refine ⟨81785797876044656397568943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54523865250696437598379295 81785797876044656397568943)
    ·
      refine ⟨122678696814066984596353415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81785797876044656397568943 122678696814066984596353415)
      ·
        refine ⟨184018045221100476894530123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122678696814066984596353415 184018045221100476894530123)
        ·
          refine ⟨276027067831650715341795185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184018045221100476894530123 276027067831650715341795185)
          ·
            refine ⟨207020300873738036506346389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276027067831650715341795185 207020300873738036506346389)
            ·
              refine ⟨9704076603456470461234987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 207020300873738036506346389 9704076603456470461234987)
              ·
                refine ⟨14556114905184705691852481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9704076603456470461234987 14556114905184705691852481)
                ·
                  refine ⟨10917086178888529268889361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14556114905184705691852481 10917086178888529268889361)
                  ·
                    refine ⟨8187814634166396951667021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10917086178888529268889361 8187814634166396951667021)
                    ·
                      refine ⟨3070430487812398856875133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8187814634166396951667021 3070430487812398856875133)
                      ·
                        rfl

theorem cell23_5979642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_5979642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979642 prefixEnd_5979642 := by exact prefixLift 5979642
  have htrace : WordTrace (prefixWord ++ tailWord_5979642) baseStart_5979642 baseEnd_5979642 := by
    simpa [prefixWord, tailWord_5979642, baseEnd_5979642] using wordTrace_append hprefix tailTrace_5979642
  have hstable : (prefixWord ++ tailWord_5979642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979642).length < 2 ^ (prefixWord ++ tailWord_5979642).sum := by decide
  have hdescent : baseEnd_5979642 < baseStart_5979642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979699 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 2, 3, 2]
def baseStart_5979699 : Nat := 118140960795 + 5979699 * 2 ^ 59
def prefixEnd_5979699 : Nat := 4983230072969 + 3 ^ 40 * 5979699 * 2
def baseEnd_5979699 : Nat := 3070459756209705133862371

theorem tailTrace_5979699 : CollatzResearch.WordTrace tailWord_5979699 prefixEnd_5979699 3070459756209705133862371 := by
  unfold tailWord_5979699
  simp only [CollatzResearch.WordTrace]
  refine ⟨218097539963579249128342151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145398359975719499418894767 218097539963579249128342151)
  ·
    refine ⟨327146309945368873692513227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218097539963579249128342151 327146309945368873692513227)
    ·
      refine ⟨490719464918053310538769841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327146309945368873692513227 490719464918053310538769841)
      ·
        refine ⟨368039598688539982904077381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490719464918053310538769841 368039598688539982904077381)
        ·
          refine ⟨69007424754101246794514509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 368039598688539982904077381 69007424754101246794514509)
          ·
            refine ⟨25877784282787967547942941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69007424754101246794514509 25877784282787967547942941)
            ·
              refine ⟨9704169106045487830478603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25877784282787967547942941 9704169106045487830478603)
              ·
                refine ⟨14556253659068231745717905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9704169106045487830478603 14556253659068231745717905)
                ·
                  refine ⟨10917190244301173809288429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14556253659068231745717905 10917190244301173809288429)
                  ·
                    refine ⟨4093946341612940178483161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10917190244301173809288429 4093946341612940178483161)
                    ·
                      refine ⟨3070459756209705133862371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4093946341612940178483161 3070459756209705133862371)
                      ·
                        rfl

theorem cell23_5979699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 3, 2].length) (baseStart_5979699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979699 prefixEnd_5979699 := by exact prefixLift 5979699
  have htrace : WordTrace (prefixWord ++ tailWord_5979699) baseStart_5979699 baseEnd_5979699 := by
    simpa [prefixWord, tailWord_5979699, baseEnd_5979699] using wordTrace_append hprefix tailTrace_5979699
  have hstable : (prefixWord ++ tailWord_5979699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979699).length < 2 ^ (prefixWord ++ tailWord_5979699).sum := by decide
  have hdescent : baseEnd_5979699 < baseStart_5979699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979706 : List Nat := [3, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3]
def baseStart_5979706 : Nat := 118140960795 + 5979706 * 2 ^ 59
def prefixEnd_5979706 : Nat := 4983230072969 + 3 ^ 40 * 5979706 * 2
def baseEnd_5979706 : Nat := 3070463350574286606474839

theorem tailTrace_5979706 : CollatzResearch.WordTrace tailWord_5979706 prefixEnd_5979706 3070463350574286606474839 := by
  unfold tailWord_5979706
  simp only [CollatzResearch.WordTrace]
  refine ⟨54524448818638472330961743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145398530183035926215897981 54524448818638472330961743)
  ·
    refine ⟨81786673227957708496442615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54524448818638472330961743 81786673227957708496442615)
    ·
      refine ⟨122680009841936562744663923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81786673227957708496442615 122680009841936562744663923)
      ·
        refine ⟨184020014762904844116995885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122680009841936562744663923 184020014762904844116995885)
        ·
          refine ⟨69007505536089316543873457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184020014762904844116995885 69007505536089316543873457)
          ·
            refine ⟨51755629152066987407905093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69007505536089316543873457 51755629152066987407905093)
            ·
              refine ⟨9704180466012560138982205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51755629152066987407905093 9704180466012560138982205)
              ·
                refine ⟨3639067674754710052118327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9704180466012560138982205 3639067674754710052118327)
                ·
                  refine ⟨5458601512132065078177491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3639067674754710052118327 5458601512132065078177491)
                  ·
                    refine ⟨8187902268198097617266237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5458601512132065078177491 8187902268198097617266237)
                    ·
                      refine ⟨3070463350574286606474839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8187902268198097617266237 3070463350574286606474839)
                      ·
                        rfl

theorem cell23_5979706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3].length) (baseStart_5979706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979706 prefixEnd_5979706 := by exact prefixLift 5979706
  have htrace : WordTrace (prefixWord ++ tailWord_5979706) baseStart_5979706 baseEnd_5979706 := by
    simpa [prefixWord, tailWord_5979706, baseEnd_5979706] using wordTrace_append hprefix tailTrace_5979706
  have hstable : (prefixWord ++ tailWord_5979706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979706).length < 2 ^ (prefixWord ++ tailWord_5979706).sum := by decide
  have hdescent : baseEnd_5979706 < baseStart_5979706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979709 : List Nat := [1, 4, 1, 3, 3, 1, 1, 3, 1, 5]
def baseStart_5979709 : Nat := 118140960795 + 5979709 * 2 ^ 59
def prefixEnd_5979709 : Nat := 4983230072969 + 3 ^ 40 * 5979709 * 2
def baseEnd_5979709 : Nat := 1023488297005416698245775

theorem tailTrace_5979709 : CollatzResearch.WordTrace tailWord_5979709 prefixEnd_5979709 1023488297005416698245775 := by
  unfold tailWord_5979709
  simp only [CollatzResearch.WordTrace]
  refine ⟨218097904693543020836206181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145398603129028680557470787 218097904693543020836206181)
  ·
    refine ⟨40893357130039316406788659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218097904693543020836206181 40893357130039316406788659)
    ·
      refine ⟨61340035695058974610182989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40893357130039316406788659 61340035695058974610182989)
      ·
        refine ⟨23002513385647115478818621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61340035695058974610182989 23002513385647115478818621)
        ·
          refine ⟨8625942519617668304556983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23002513385647115478818621 8625942519617668304556983)
          ·
            refine ⟨12938913779426502456835475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8625942519617668304556983 12938913779426502456835475)
            ·
              refine ⟨19408370669139753685253213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12938913779426502456835475 19408370669139753685253213)
              ·
                refine ⟨7278139000927407631969955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19408370669139753685253213 7278139000927407631969955)
                ·
                  refine ⟨10917208501391111447954933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7278139000927407631969955 10917208501391111447954933)
                  ·
                    refine ⟨1023488297005416698245775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10917208501391111447954933 1023488297005416698245775)
                    ·
                      rfl

theorem cell23_5979709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_5979709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979709 prefixEnd_5979709 := by exact prefixLift 5979709
  have htrace : WordTrace (prefixWord ++ tailWord_5979709) baseStart_5979709 baseEnd_5979709 := by
    simpa [prefixWord, tailWord_5979709, baseEnd_5979709] using wordTrace_append hprefix tailTrace_5979709
  have hstable : (prefixWord ++ tailWord_5979709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979709).length < 2 ^ (prefixWord ++ tailWord_5979709).sum := by decide
  have hdescent : baseEnd_5979709 < baseStart_5979709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979722 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 4, 4]
def baseStart_5979722 : Nat := 118140960795 + 5979722 * 2 ^ 59
def prefixEnd_5979722 : Nat := 4983230072969 + 3 ^ 40 * 5979722 * 2
def baseEnd_5979722 : Nat := 1023490522088252847958255

theorem tailTrace_5979722 : CollatzResearch.WordTrace tailWord_5979722 prefixEnd_5979722 1023490522088252847958255 := by
  unfold tailWord_5979722
  simp only [CollatzResearch.WordTrace]
  refine ⟨54524594710623981014107355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145398919228330616037619613 54524594710623981014107355)
  ·
    refine ⟨81786892065935971521161033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54524594710623981014107355 81786892065935971521161033)
    ·
      refine ⟨61340169049451978640870775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81786892065935971521161033 61340169049451978640870775)
      ·
        refine ⟨92010253574177967961306163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61340169049451978640870775 92010253574177967961306163)
        ·
          refine ⟨138015380361266951941959245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92010253574177967961306163 138015380361266951941959245)
          ·
            refine ⟨51755767635475106978234717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138015380361266951941959245 51755767635475106978234717)
            ·
              refine ⟨19408412863303165116838019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51755767635475106978234717 19408412863303165116838019)
              ·
                refine ⟨29112619294954747675257029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19408412863303165116838019 29112619294954747675257029)
                ·
                  refine ⟨5458616117804015189110693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29112619294954747675257029 5458616117804015189110693)
                  ·
                    refine ⟨1023490522088252847958255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5458616117804015189110693 1023490522088252847958255)
                    ·
                      rfl

theorem cell23_5979722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_5979722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979722 prefixEnd_5979722 := by exact prefixLift 5979722
  have htrace : WordTrace (prefixWord ++ tailWord_5979722) baseStart_5979722 baseEnd_5979722 := by
    simpa [prefixWord, tailWord_5979722, baseEnd_5979722] using wordTrace_append hprefix tailTrace_5979722
  have hstable : (prefixWord ++ tailWord_5979722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979722).length < 2 ^ (prefixWord ++ tailWord_5979722).sum := by decide
  have hdescent : baseEnd_5979722 < baseStart_5979722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979732 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_5979732 : Nat := 118140960795 + 5979732 * 2 ^ 59
def prefixEnd_5979732 : Nat := 4983230072969 + 3 ^ 40 * 5979732 * 2
def baseEnd_5979732 : Nat := 3070476701071303504749719

theorem tailTrace_5979732 : CollatzResearch.WordTrace tailWord_5979732 prefixEnd_5979732 3070476701071303504749719 := by
  unfold tailWord_5979732
  simp only [CollatzResearch.WordTrace]
  refine ⟨109049371786229847882146725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145399162381639797176195633 109049371786229847882146725)
  ·
    refine ⟨20446757209918096477902511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109049371786229847882146725 20446757209918096477902511)
    ·
      refine ⟨30670135814877144716853767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20446757209918096477902511 30670135814877144716853767)
      ·
        refine ⟨46005203722315717075280651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30670135814877144716853767 46005203722315717075280651)
        ·
          refine ⟨69007805583473575612920977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46005203722315717075280651 69007805583473575612920977)
          ·
            refine ⟨51755854187605181709690733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69007805583473575612920977 51755854187605181709690733)
            ·
              refine ⟨19408445320351943141134025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51755854187605181709690733 19408445320351943141134025)
              ·
                refine ⟨14556333990263957355850519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19408445320351943141134025 14556333990263957355850519)
                ·
                  refine ⟨21834500985395936033775779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14556333990263957355850519 21834500985395936033775779)
                  ·
                    refine ⟨32751751478093904050663669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21834500985395936033775779 32751751478093904050663669)
                    ·
                      refine ⟨3070476701071303504749719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32751751478093904050663669 3070476701071303504749719)
                      ·
                        rfl

theorem cell23_5979732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_5979732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979732 prefixEnd_5979732 := by exact prefixLift 5979732
  have htrace : WordTrace (prefixWord ++ tailWord_5979732) baseStart_5979732 baseEnd_5979732 := by
    simpa [prefixWord, tailWord_5979732, baseEnd_5979732] using wordTrace_append hprefix tailTrace_5979732
  have hstable : (prefixWord ++ tailWord_5979732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979732).length < 2 ^ (prefixWord ++ tailWord_5979732).sum := by decide
  have hdescent : baseEnd_5979732 < baseStart_5979732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979749 : List Nat := [1, 3, 1, 3, 3, 1, 1, 4, 1, 2, 3]
def baseStart_5979749 : Nat := 118140960795 + 5979749 * 2 ^ 59
def prefixEnd_5979749 : Nat := 4983230072969 + 3 ^ 40 * 5979749 * 2
def baseEnd_5979749 : Nat := 3070485430242429938237141

theorem tailTrace_5979749 : CollatzResearch.WordTrace tailWord_5979749 prefixEnd_5979749 3070485430242429938237141 := by
  unfold tailWord_5979749
  simp only [CollatzResearch.WordTrace]
  refine ⟨218099363613398107667662301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145399575742265405111774867 218099363613398107667662301)
  ·
    refine ⟨81787261355024290375373363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218099363613398107667662301 81787261355024290375373363)
    ·
      refine ⟨122680892032536435563060045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81787261355024290375373363 122680892032536435563060045)
      ·
        refine ⟨46005334512201163336147517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122680892032536435563060045 46005334512201163336147517)
        ·
          refine ⟨17252000442075436251055319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46005334512201163336147517 17252000442075436251055319)
          ·
            refine ⟨25878000663113154376582979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17252000442075436251055319 25878000663113154376582979)
            ·
              refine ⟨38817000994669731564874469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25878000663113154376582979 38817000994669731564874469)
              ·
                refine ⟨7278187686500574668413963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38817000994669731564874469 7278187686500574668413963)
                ·
                  refine ⟨10917281529750862002620945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7278187686500574668413963 10917281529750862002620945)
                  ·
                    refine ⟨8187961147313146501965709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10917281529750862002620945 8187961147313146501965709)
                    ·
                      refine ⟨3070485430242429938237141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8187961147313146501965709 3070485430242429938237141)
                      ·
                        rfl

theorem cell23_5979749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_5979749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979749 prefixEnd_5979749 := by exact prefixLift 5979749
  have htrace : WordTrace (prefixWord ++ tailWord_5979749) baseStart_5979749 baseEnd_5979749 := by
    simpa [prefixWord, tailWord_5979749, baseEnd_5979749] using wordTrace_append hprefix tailTrace_5979749
  have hstable : (prefixWord ++ tailWord_5979749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979749).length < 2 ^ (prefixWord ++ tailWord_5979749).sum := by decide
  have hdescent : baseEnd_5979749 < baseStart_5979749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979752 : List Nat := [2, 1, 4, 3, 1, 2, 1, 9]
def baseStart_5979752 : Nat := 118140960795 + 5979752 * 2 ^ 59
def prefixEnd_5979752 : Nat := 4983230072969 + 3 ^ 40 * 5979752 * 2
def baseEnd_5979752 : Nat := 113721739654977534314801

theorem tailTrace_5979752 : CollatzResearch.WordTrace tailWord_5979752 prefixEnd_5979752 113721739654977534314801 := by
  unfold tailWord_5979752
  simp only [CollatzResearch.WordTrace]
  refine ⟨109049736516193619590010755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145399648688258159453347673 109049736516193619590010755)
  ·
    refine ⟨163574604774290429385016133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109049736516193619590010755 163574604774290429385016133)
    ·
      refine ⟨30670238395179455509690525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163574604774290429385016133 30670238395179455509690525)
      ·
        refine ⟨11501339398192295816133947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30670238395179455509690525 11501339398192295816133947)
        ·
          refine ⟨17252009097288443724200921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11501339398192295816133947 17252009097288443724200921)
          ·
            refine ⟨12939006822966332793150691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17252009097288443724200921 12939006822966332793150691)
            ·
              refine ⟨19408510234449499189726037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12939006822966332793150691 19408510234449499189726037)
              ·
                refine ⟨113721739654977534314801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19408510234449499189726037 113721739654977534314801)
                ·
                  rfl

theorem cell23_5979752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 9].length) (baseStart_5979752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979752 prefixEnd_5979752 := by exact prefixLift 5979752
  have htrace : WordTrace (prefixWord ++ tailWord_5979752) baseStart_5979752 baseEnd_5979752 := by
    simpa [prefixWord, tailWord_5979752, baseEnd_5979752] using wordTrace_append hprefix tailTrace_5979752
  have hstable : (prefixWord ++ tailWord_5979752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979752).length < 2 ^ (prefixWord ++ tailWord_5979752).sum := by decide
  have hdescent : baseEnd_5979752 < baseStart_5979752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979766 : List Nat := [5, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_5979766 : Nat := 118140960795 + 5979766 * 2 ^ 59
def prefixEnd_5979766 : Nat := 4983230072969 + 3 ^ 40 * 5979766 * 2
def baseEnd_5979766 : Nat := 3070494159413556371724563

theorem tailTrace_5979766 : CollatzResearch.WordTrace tailWord_5979766 prefixEnd_5979766 3070494159413556371724563 := by
  unfold tailWord_5979766
  simp only [CollatzResearch.WordTrace]
  refine ⟨13631248978396032473189447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145399989102891013047354101 13631248978396032473189447)
  ·
    refine ⟨20446873467594048709784171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13631248978396032473189447 20446873467594048709784171)
    ·
      refine ⟨30670310201391073064676257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20446873467594048709784171 30670310201391073064676257)
      ·
        refine ⟨23002732651043304798507193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30670310201391073064676257 23002732651043304798507193)
        ·
          refine ⟨17252049488282478598880395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23002732651043304798507193 17252049488282478598880395)
          ·
            refine ⟨25878074232423717898320593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17252049488282478598880395 25878074232423717898320593)
            ·
              refine ⟨19408555674317788423740445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25878074232423717898320593 19408555674317788423740445)
              ·
                refine ⟨7278208377869170658902667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19408555674317788423740445 7278208377869170658902667)
                ·
                  refine ⟨10917312566803755988354001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7278208377869170658902667 10917312566803755988354001)
                  ·
                    refine ⟨8187984425102816991265501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10917312566803755988354001 8187984425102816991265501)
                    ·
                      refine ⟨3070494159413556371724563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8187984425102816991265501 3070494159413556371724563)
                      ·
                        rfl

theorem cell23_5979766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_5979766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979766 prefixEnd_5979766 := by exact prefixLift 5979766
  have htrace : WordTrace (prefixWord ++ tailWord_5979766) baseStart_5979766 baseEnd_5979766 := by
    simpa [prefixWord, tailWord_5979766, baseEnd_5979766] using wordTrace_append hprefix tailTrace_5979766
  have hstable : (prefixWord ++ tailWord_5979766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979766).length < 2 ^ (prefixWord ++ tailWord_5979766).sum := by decide
  have hdescent : baseEnd_5979766 < baseStart_5979766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979779 : List Nat := [1, 1, 1, 3, 3, 1, 1, 6, 2, 1, 3]
def baseStart_5979779 : Nat := 118140960795 + 5979779 * 2 ^ 59
def prefixEnd_5979779 : Nat := 4983230072969 + 3 ^ 40 * 5979779 * 2
def baseEnd_5979779 : Nat := 3070500834662064820862003

theorem tailTrace_5979779 : CollatzResearch.WordTrace tailWord_5979779 prefixEnd_5979779 3070500834662064820862003 := by
  unfold tailWord_5979779
  simp only [CollatzResearch.WordTrace]
  refine ⟨218100457803289422791254391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145400305202192948527502927 218100457803289422791254391)
  ·
    refine ⟨327150686704934134186881587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218100457803289422791254391 327150686704934134186881587)
    ·
      refine ⟨490726030057401201280322381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327150686704934134186881587 490726030057401201280322381)
      ·
        refine ⟨184022261271525450480120893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 490726030057401201280322381 184022261271525450480120893)
        ·
          refine ⟨69008347976822043930045335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184022261271525450480120893 69008347976822043930045335)
          ·
            refine ⟨103512521965233065895068003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69008347976822043930045335 103512521965233065895068003)
            ·
              refine ⟨155268782947849598842602005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103512521965233065895068003 155268782947849598842602005)
              ·
                refine ⟨7278224200680449945746969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 155268782947849598842602005 7278224200680449945746969)
                ·
                  refine ⟨5458668150510337459310227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7278224200680449945746969 5458668150510337459310227)
                  ·
                    refine ⟨8188002225765506188965341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5458668150510337459310227 8188002225765506188965341)
                    ·
                      refine ⟨3070500834662064820862003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8188002225765506188965341 3070500834662064820862003)
                      ·
                        rfl

theorem cell23_5979779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 1, 3].length) (baseStart_5979779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979779 prefixEnd_5979779 := by exact prefixLift 5979779
  have htrace : WordTrace (prefixWord ++ tailWord_5979779) baseStart_5979779 baseEnd_5979779 := by
    simpa [prefixWord, tailWord_5979779, baseEnd_5979779] using wordTrace_append hprefix tailTrace_5979779
  have hstable : (prefixWord ++ tailWord_5979779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979779).length < 2 ^ (prefixWord ++ tailWord_5979779).sum := by decide
  have hdescent : baseEnd_5979779 < baseStart_5979779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979780 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 3, 2, 2]
def baseStart_5979780 : Nat := 118140960795 + 5979780 * 2 ^ 59
def prefixEnd_5979780 : Nat := 4983230072969 + 3 ^ 40 * 5979780 * 2
def baseEnd_5979780 : Nat := 3070501348142719316949499

theorem tailTrace_5979780 : CollatzResearch.WordTrace tailWord_5979780 prefixEnd_5979780 3070501348142719316949499 := by
  unfold tailWord_5979780
  simp only [CollatzResearch.WordTrace]
  refine ⟨109050247138142899981020397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145400329517523866641360529 109050247138142899981020397)
  ·
    refine ⟨40893842676803587492882649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109050247138142899981020397 40893842676803587492882649)
    ·
      refine ⟨30670382007602690619661987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40893842676803587492882649 30670382007602690619661987)
      ·
        refine ⟨46005573011404035929492981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30670382007602690619661987 46005573011404035929492981)
        ·
          refine ⟨4313022469819128368389967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46005573011404035929492981 4313022469819128368389967)
          ·
            refine ⟨6469533704728692552584951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4313022469819128368389967 6469533704728692552584951)
            ·
              refine ⟨9704300557093038828877427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6469533704728692552584951 9704300557093038828877427)
              ·
                refine ⟨14556450835639558243316141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9704300557093038828877427 14556450835639558243316141)
                ·
                  refine ⟨5458669063364834341243553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14556450835639558243316141 5458669063364834341243553)
                  ·
                    refine ⟨4094001797523625755932665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5458669063364834341243553 4094001797523625755932665)
                    ·
                      refine ⟨3070501348142719316949499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4094001797523625755932665 3070501348142719316949499)
                      ·
                        rfl

theorem cell23_5979780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_5979780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979780 prefixEnd_5979780 := by exact prefixLift 5979780
  have htrace : WordTrace (prefixWord ++ tailWord_5979780) baseStart_5979780 baseEnd_5979780 := by
    simpa [prefixWord, tailWord_5979780, baseEnd_5979780] using wordTrace_append hprefix tailTrace_5979780
  have hstable : (prefixWord ++ tailWord_5979780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979780).length < 2 ^ (prefixWord ++ tailWord_5979780).sum := by decide
  have hdescent : baseEnd_5979780 < baseStart_5979780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979830 : List Nat := [5, 1, 3, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_5979830 : Nat := 118140960795 + 5979830 * 2 ^ 59
def prefixEnd_5979830 : Nat := 4983230072969 + 3 ^ 40 * 5979830 * 2
def baseEnd_5979830 : Nat := 3070527022175444121324269

theorem tailTrace_5979830 : CollatzResearch.WordTrace tailWord_5979830 prefixEnd_5979830 3070527022175444121324269 := by
  unfold tailWord_5979830
  simp only [CollatzResearch.WordTrace]
  refine ⟨13631394870381541156335059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145401545284069772334240629 13631394870381541156335059)
  ·
    refine ⟨20447092305572311734502589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13631394870381541156335059 20447092305572311734502589)
    ·
      refine ⟨7667659614589616900438471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20447092305572311734502589 7667659614589616900438471)
      ·
        refine ⟨11501489421884425350657707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7667659614589616900438471 11501489421884425350657707)
        ·
          refine ⟨17252234132826638025986561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11501489421884425350657707 17252234132826638025986561)
          ·
            refine ⟨12939175599619978519489921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17252234132826638025986561 12939175599619978519489921)
            ·
              refine ⟨9704381699714983889617441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12939175599619978519489921 9704381699714983889617441)
              ·
                refine ⟨7278286274786237917213081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9704381699714983889617441 7278286274786237917213081)
                ·
                  refine ⟨5458714706089678437909811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7278286274786237917213081 5458714706089678437909811)
                  ·
                    refine ⟨8188072059134517656864717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5458714706089678437909811 8188072059134517656864717)
                    ·
                      refine ⟨3070527022175444121324269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8188072059134517656864717 3070527022175444121324269)
                      ·
                        rfl

theorem cell23_5979830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_5979830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979830 prefixEnd_5979830 := by exact prefixLift 5979830
  have htrace : WordTrace (prefixWord ++ tailWord_5979830) baseStart_5979830 baseEnd_5979830 := by
    simpa [prefixWord, tailWord_5979830, baseEnd_5979830] using wordTrace_append hprefix tailTrace_5979830
  have hstable : (prefixWord ++ tailWord_5979830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979830).length < 2 ^ (prefixWord ++ tailWord_5979830).sum := by decide
  have hdescent : baseEnd_5979830 < baseStart_5979830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979835 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 7]
def baseStart_5979835 : Nat := 118140960795 + 5979835 * 2 ^ 59
def prefixEnd_5979835 : Nat := 4983230072969 + 3 ^ 40 * 5979835 * 2
def baseEnd_5979835 : Nat := 3070529589578716601761745

theorem tailTrace_5979835 : CollatzResearch.WordTrace tailWord_5979835 prefixEnd_5979835 3070529589578716601761745 := by
  unfold tailWord_5979835
  simp only [CollatzResearch.WordTrace]
  refine ⟨218102500291086544355292959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145401666860724362903528639 218102500291086544355292959)
  ·
    refine ⟨327153750436629816532939439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218102500291086544355292959 327153750436629816532939439)
    ·
      refine ⟨490730625654944724799409159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327153750436629816532939439 490730625654944724799409159)
      ·
        refine ⟨736095938482417087199113739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490730625654944724799409159 736095938482417087199113739)
        ·
          refine ⟨1104143907723625630798670609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736095938482417087199113739 1104143907723625630798670609)
          ·
            refine ⟨828107930792719223099002957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1104143907723625630798670609 828107930792719223099002957)
            ·
              refine ⟨310540474047269708662126109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 828107930792719223099002957 310540474047269708662126109)
              ·
                refine ⟨116452677767726140748297291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310540474047269708662126109 116452677767726140748297291)
                ·
                  refine ⟨174679016651589211122445937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116452677767726140748297291 174679016651589211122445937)
                  ·
                    refine ⟨131009262488691908341834453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 174679016651589211122445937 131009262488691908341834453)
                    ·
                      refine ⟨3070529589578716601761745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131009262488691908341834453 3070529589578716601761745)
                      ·
                        rfl

theorem cell23_5979835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 7].length) (baseStart_5979835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979835 prefixEnd_5979835 := by exact prefixLift 5979835
  have htrace : WordTrace (prefixWord ++ tailWord_5979835) baseStart_5979835 baseEnd_5979835 := by
    simpa [prefixWord, tailWord_5979835, baseEnd_5979835] using wordTrace_append hprefix tailTrace_5979835
  have hstable : (prefixWord ++ tailWord_5979835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979835).length < 2 ^ (prefixWord ++ tailWord_5979835).sum := by decide
  have hdescent : baseEnd_5979835 < baseStart_5979835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979846 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_5979846 : Nat := 118140960795 + 5979846 * 2 ^ 59
def prefixEnd_5979846 : Nat := 4983230072969 + 3 ^ 40 * 5979846 * 2
def baseEnd_5979846 : Nat := 1023511745955305352908065

theorem tailTrace_5979846 : CollatzResearch.WordTrace tailWord_5979846 prefixEnd_5979846 1023511745955305352908065 := by
  unfold tailWord_5979846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6815715671688959163560731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145401934329364462155962261 6815715671688959163560731)
  ·
    refine ⟨10223573507533438745341097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6815715671688959163560731 10223573507533438745341097)
    ·
      refine ⟨7667680130650079059005823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10223573507533438745341097 7667680130650079059005823)
      ·
        refine ⟨11501520195975118588508735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7667680130650079059005823 11501520195975118588508735)
        ·
          refine ⟨17252280293962677882763103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11501520195975118588508735 17252280293962677882763103)
          ·
            refine ⟨25878420440944016824144655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17252280293962677882763103 25878420440944016824144655)
            ·
              refine ⟨38817630661416025236216983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25878420440944016824144655 38817630661416025236216983)
              ·
                refine ⟨58226445992124037854325475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38817630661416025236216983 58226445992124037854325475)
                ·
                  refine ⟨87339668988186056781488213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58226445992124037854325475 87339668988186056781488213)
                  ·
                    refine ⟨1023511745955305352908065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87339668988186056781488213 1023511745955305352908065)
                    ·
                      rfl

theorem cell23_5979846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_5979846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979846 prefixEnd_5979846 := by exact prefixLift 5979846
  have htrace : WordTrace (prefixWord ++ tailWord_5979846) baseStart_5979846 baseEnd_5979846 := by
    simpa [prefixWord, tailWord_5979846, baseEnd_5979846] using wordTrace_append hprefix tailTrace_5979846
  have hstable : (prefixWord ++ tailWord_5979846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979846).length < 2 ^ (prefixWord ++ tailWord_5979846).sum := by decide
  have hdescent : baseEnd_5979846 < baseStart_5979846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979853 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_5979853 : Nat := 118140960795 + 5979853 * 2 ^ 59
def prefixEnd_5979853 : Nat := 4983230072969 + 3 ^ 40 * 5979853 * 2
def baseEnd_5979853 : Nat := 3070538832230497531336663

theorem tailTrace_5979853 : CollatzResearch.WordTrace tailWord_5979853 prefixEnd_5979853 3070538832230497531336663 := by
  unfold tailWord_5979853
  simp only [CollatzResearch.WordTrace]
  refine ⟨218103156805021333429448213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145402104536680888952965475 218103156805021333429448213)
  ·
    refine ⟨10223585475235375004505385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 218103156805021333429448213 10223585475235375004505385)
    ·
      refine ⟨7667689106426531253379039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10223585475235375004505385 7667689106426531253379039)
      ·
        refine ⟨11501533659639796880068559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7667689106426531253379039 11501533659639796880068559)
        ·
          refine ⟨17252300489459695320102839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11501533659639796880068559 17252300489459695320102839)
          ·
            refine ⟨25878450734189542980154259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17252300489459695320102839 25878450734189542980154259)
            ·
              refine ⟨38817676101284314470231389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25878450734189542980154259 38817676101284314470231389)
              ·
                refine ⟨14556628537981617926336771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38817676101284314470231389 14556628537981617926336771)
                ·
                  refine ⟨21834942806972426889505157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14556628537981617926336771 21834942806972426889505157)
                  ·
                    refine ⟨4094051776307330041782217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21834942806972426889505157 4094051776307330041782217)
                    ·
                      refine ⟨3070538832230497531336663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4094051776307330041782217 3070538832230497531336663)
                      ·
                        rfl

theorem cell23_5979853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_5979853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979853 prefixEnd_5979853 := by exact prefixLift 5979853
  have htrace : WordTrace (prefixWord ++ tailWord_5979853) baseStart_5979853 baseEnd_5979853 := by
    simpa [prefixWord, tailWord_5979853, baseEnd_5979853] using wordTrace_append hprefix tailTrace_5979853
  have hstable : (prefixWord ++ tailWord_5979853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979853).length < 2 ^ (prefixWord ++ tailWord_5979853).sum := by decide
  have hdescent : baseEnd_5979853 < baseStart_5979853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979882 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_5979882 : Nat := 118140960795 + 5979882 * 2 ^ 59
def prefixEnd_5979882 : Nat := 4983230072969 + 3 ^ 40 * 5979882 * 2
def baseEnd_5979882 : Nat := 3070553723169477917874029

theorem tailTrace_5979882 : CollatzResearch.WordTrace tailWord_5979882 prefixEnd_5979882 3070553723169477917874029 := by
  unfold tailWord_5979882
  simp only [CollatzResearch.WordTrace]
  refine ⟨54526053630479067845563475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145402809681277514254835933 54526053630479067845563475)
  ·
    refine ⟨81789080445718601768345213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54526053630479067845563475 81789080445718601768345213)
    ·
      refine ⟨30670905167144475663129455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81789080445718601768345213 30670905167144475663129455)
      ·
        refine ⟨46006357750716713494694183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30670905167144475663129455 46006357750716713494694183)
        ·
          refine ⟨69009536626075070242041275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46006357750716713494694183 69009536626075070242041275)
          ·
            refine ⟨103514304939112605363061913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69009536626075070242041275 103514304939112605363061913)
            ·
              refine ⟨77635728704334454022296435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103514304939112605363061913 77635728704334454022296435)
              ·
                refine ⟨116453593056501681033444653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77635728704334454022296435 116453593056501681033444653)
                ·
                  refine ⟨43670097396188130387541745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116453593056501681033444653 43670097396188130387541745)
                  ·
                    refine ⟨32752573047141097790656309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43670097396188130387541745 32752573047141097790656309)
                    ·
                      refine ⟨3070553723169477917874029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32752573047141097790656309 3070553723169477917874029)
                      ·
                        rfl

theorem cell23_5979882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_5979882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979882 prefixEnd_5979882 := by exact prefixLift 5979882
  have htrace : WordTrace (prefixWord ++ tailWord_5979882) baseStart_5979882 baseEnd_5979882 := by
    simpa [prefixWord, tailWord_5979882, baseEnd_5979882] using wordTrace_append hprefix tailTrace_5979882
  have hstable : (prefixWord ++ tailWord_5979882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979882).length < 2 ^ (prefixWord ++ tailWord_5979882).sum := by decide
  have hdescent : baseEnd_5979882 < baseStart_5979882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5979932 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 10]
def baseStart_5979932 : Nat := 118140960795 + 5979932 * 2 ^ 59
def prefixEnd_5979932 : Nat := 4983230072969 + 3 ^ 40 * 5979932 * 2
def baseEnd_5979932 : Nat := 341175488578022524694311

theorem tailTrace_5979932 : CollatzResearch.WordTrace tailWord_5979932 prefixEnd_5979932 341175488578022524694311 := by
  unfold tailWord_5979932
  simp only [CollatzResearch.WordTrace]
  refine ⟨109053019085867564960787025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145404025447823419947716033 109053019085867564960787025)
  ·
    refine ⟨81789764314400673720590269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109053019085867564960787025 81789764314400673720590269)
    ·
      refine ⟨30671161617900252645221351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81789764314400673720590269 30671161617900252645221351)
      ·
        refine ⟨46006742426850378967832027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30671161617900252645221351 46006742426850378967832027)
        ·
          refine ⟨69010113640275568451748041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46006742426850378967832027 69010113640275568451748041)
          ·
            refine ⟨51757585230206676338811031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69010113640275568451748041 51757585230206676338811031)
            ·
              refine ⟨77636377845310014508216547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51757585230206676338811031 77636377845310014508216547)
              ·
                refine ⟨116454566767965021762324821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77636377845310014508216547 116454566767965021762324821)
                ·
                  refine ⟨341175488578022524694311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 116454566767965021762324821 341175488578022524694311)
                  ·
                    rfl

theorem cell23_5979932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 10].length) (baseStart_5979932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5979932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5979932 prefixEnd_5979932 := by exact prefixLift 5979932
  have htrace : WordTrace (prefixWord ++ tailWord_5979932) baseStart_5979932 baseEnd_5979932 := by
    simpa [prefixWord, tailWord_5979932, baseEnd_5979932] using wordTrace_append hprefix tailTrace_5979932
  have hstable : (prefixWord ++ tailWord_5979932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5979932).length < 2 ^ (prefixWord ++ tailWord_5979932).sum := by decide
  have hdescent : baseEnd_5979932 < baseStart_5979932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5979932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
