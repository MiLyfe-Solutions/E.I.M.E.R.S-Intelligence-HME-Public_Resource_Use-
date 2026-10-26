import V185TrunkScan23Chunk0503

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2981303 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 3]
def baseStart_2981303 : Nat := 118140960795 + 2981303 * 2 ^ 59
def prefixEnd_2981303 : Nat := 4983230072969 + 3 ^ 40 * 2981303 * 2
def baseEnd_2981303 : Nat := 1530841415691254372001743

theorem tailTrace_2981303 : CollatzResearch.WordTrace tailWord_2981303 prefixEnd_2981303 1530841415691254372001743 := by
  unfold tailWord_2981303
  simp only [CollatzResearch.WordTrace]
  refine ⟨108737053518255871860732563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72491369012170581240488375 108737053518255871860732563)
  ·
    refine ⟨163105580277383807791098845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108737053518255871860732563 163105580277383807791098845)
    ·
      refine ⟨61164592604018927921662067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163105580277383807791098845 61164592604018927921662067)
      ·
        refine ⟨91746888906028391882493101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61164592604018927921662067 91746888906028391882493101)
        ·
          refine ⟨34405083339760646955934913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91746888906028391882493101 34405083339760646955934913)
          ·
            refine ⟨25803812504820485216951185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34405083339760646955934913 25803812504820485216951185)
            ·
              refine ⟨19352859378615363912713389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25803812504820485216951185 19352859378615363912713389)
              ·
                refine ⟨7257322266980761467267521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19352859378615363912713389 7257322266980761467267521)
                ·
                  refine ⟨5442991700235571100450641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7257322266980761467267521 5442991700235571100450641)
                  ·
                    refine ⟨4082243775176678325337981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5442991700235571100450641 4082243775176678325337981)
                    ·
                      refine ⟨1530841415691254372001743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4082243775176678325337981 1530841415691254372001743)
                      ·
                        rfl

theorem cell23_2981303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_2981303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981303 prefixEnd_2981303 := by exact prefixLift 2981303
  have htrace : WordTrace (prefixWord ++ tailWord_2981303) baseStart_2981303 baseEnd_2981303 := by
    simpa [prefixWord, tailWord_2981303, baseEnd_2981303] using wordTrace_append hprefix tailTrace_2981303
  have hstable : (prefixWord ++ tailWord_2981303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981303).length < 2 ^ (prefixWord ++ tailWord_2981303).sum := by decide
  have hdescent : baseEnd_2981303 < baseStart_2981303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981326 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_2981326 : Nat := 118140960795 + 2981326 * 2 ^ 59
def prefixEnd_2981326 : Nat := 4983230072969 + 3 ^ 40 * 2981326 * 2
def baseEnd_2981326 : Nat := 1530853225746307782014137

theorem tailTrace_2981326 : CollatzResearch.WordTrace tailWord_2981326 prefixEnd_2981326 1530853225746307782014137 := by
  unfold tailWord_2981326
  simp only [CollatzResearch.WordTrace]
  refine ⟨13592236549646568348602479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72491928264781697859213221 13592236549646568348602479)
  ·
    refine ⟨20388354824469852522903719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13592236549646568348602479 20388354824469852522903719)
    ·
      refine ⟨30582532236704778784355579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20388354824469852522903719 30582532236704778784355579)
      ·
        refine ⟨45873798355057168176533369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30582532236704778784355579 45873798355057168176533369)
        ·
          refine ⟨34405348766292876132400027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45873798355057168176533369 34405348766292876132400027)
          ·
            refine ⟨51608023149439314198600041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34405348766292876132400027 51608023149439314198600041)
            ·
              refine ⟨38706017362079485648950031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51608023149439314198600041 38706017362079485648950031)
              ·
                refine ⟨58059026043119228473425047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38706017362079485648950031 58059026043119228473425047)
                ·
                  refine ⟨87088539064678842710137571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58059026043119228473425047 87088539064678842710137571)
                  ·
                    refine ⟨130632808597018264065206357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87088539064678842710137571 130632808597018264065206357)
                    ·
                      refine ⟨1530853225746307782014137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 130632808597018264065206357 1530853225746307782014137)
                      ·
                        rfl

theorem cell23_2981326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_2981326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981326 prefixEnd_2981326 := by exact prefixLift 2981326
  have htrace : WordTrace (prefixWord ++ tailWord_2981326) baseStart_2981326 baseEnd_2981326 := by
    simpa [prefixWord, tailWord_2981326, baseEnd_2981326] using wordTrace_append hprefix tailTrace_2981326
  have hstable : (prefixWord ++ tailWord_2981326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981326).length < 2 ^ (prefixWord ++ tailWord_2981326).sum := by decide
  have hdescent : baseEnd_2981326 < baseStart_2981326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981360 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 2, 3, 2]
def baseStart_2981360 : Nat := 118140960795 + 2981360 * 2 ^ 59
def prefixEnd_2981360 : Nat := 4983230072969 + 3 ^ 40 * 2981360 * 2
def baseEnd_2981360 : Nat := 1530870684088560648988981

theorem tailTrace_2981360 : CollatzResearch.WordTrace tailWord_2981360 prefixEnd_2981360 1530870684088560648988981 := by
  unfold tailWord_2981360
  simp only [CollatzResearch.WordTrace]
  refine ⟨54369566239524685297778767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72492754986032913730371689 54369566239524685297778767)
  ·
    refine ⟨81554349359287027946668151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54369566239524685297778767 81554349359287027946668151)
    ·
      refine ⟨122331524038930541920002227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81554349359287027946668151 122331524038930541920002227)
      ·
        refine ⟨183497286058395812880003341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122331524038930541920002227 183497286058395812880003341)
        ·
          refine ⟨68811482271898429830001253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183497286058395812880003341 68811482271898429830001253)
          ·
            refine ⟨12902152925980955593125235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68811482271898429830001253 12902152925980955593125235)
            ·
              refine ⟨19353229388971433389687853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12902152925980955593125235 19353229388971433389687853)
              ·
                refine ⟨7257461020864287521132945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19353229388971433389687853 7257461020864287521132945)
                ·
                  refine ⟨5443095765648215640849709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7257461020864287521132945 5443095765648215640849709)
                  ·
                    refine ⟨2041160912118080865318641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5443095765648215640849709 2041160912118080865318641)
                    ·
                      refine ⟨1530870684088560648988981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2041160912118080865318641 1530870684088560648988981)
                      ·
                        rfl

theorem cell23_2981360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 2, 3, 2].length) (baseStart_2981360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981360 prefixEnd_2981360 := by exact prefixLift 2981360
  have htrace : WordTrace (prefixWord ++ tailWord_2981360) baseStart_2981360 baseEnd_2981360 := by
    simpa [prefixWord, tailWord_2981360, baseEnd_2981360] using wordTrace_append hprefix tailTrace_2981360
  have hstable : (prefixWord ++ tailWord_2981360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981360).length < 2 ^ (prefixWord ++ tailWord_2981360).sum := by decide
  have hdescent : baseEnd_2981360 < baseStart_2981360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981370 : List Nat := [3, 1, 1, 1, 1, 2, 7, 1, 1, 5]
def baseStart_2981370 : Nat := 118140960795 + 2981370 * 2 ^ 59
def prefixEnd_2981370 : Nat := 4983230072969 + 3 ^ 40 * 2981370 * 2
def baseEnd_2981370 : Nat := 510291939631701869954645

theorem tailTrace_2981370 : CollatzResearch.WordTrace tailWord_2981370 prefixEnd_2981370 510291939631701869954645 := by
  unfold tailWord_2981370
  simp only [CollatzResearch.WordTrace]
  refine ⟨27184874302253285575855391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72492998139342094868947709 27184874302253285575855391)
  ·
    refine ⟨40777311453379928363783087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27184874302253285575855391 40777311453379928363783087)
    ·
      refine ⟨61165967180069892545674631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40777311453379928363783087 61165967180069892545674631)
      ·
        refine ⟨91748950770104838818511947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61165967180069892545674631 91748950770104838818511947)
        ·
          refine ⟨137623426155157258227767921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91748950770104838818511947 137623426155157258227767921)
          ·
            refine ⟨103217569616367943670825941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137623426155157258227767921 103217569616367943670825941)
            ·
              refine ⟨2419161787883623679784983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 103217569616367943670825941 2419161787883623679784983)
              ·
                refine ⟨3628742681825435519677475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419161787883623679784983 3628742681825435519677475)
                ·
                  refine ⟨5443114022738153279516213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3628742681825435519677475 5443114022738153279516213)
                  ·
                    refine ⟨510291939631701869954645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5443114022738153279516213 510291939631701869954645)
                    ·
                      rfl

theorem cell23_2981370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 1, 5].length) (baseStart_2981370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981370 prefixEnd_2981370 := by exact prefixLift 2981370
  have htrace : WordTrace (prefixWord ++ tailWord_2981370) baseStart_2981370 baseEnd_2981370 := by
    simpa [prefixWord, tailWord_2981370, baseEnd_2981370] using wordTrace_append hprefix tailTrace_2981370
  have hstable : (prefixWord ++ tailWord_2981370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981370).length < 2 ^ (prefixWord ++ tailWord_2981370).sum := by decide
  have hdescent : baseEnd_2981370 < baseStart_2981370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981384 : List Nat := [2, 1, 3, 2, 1, 1, 6, 2, 1, 1, 3]
def baseStart_2981384 : Nat := 118140960795 + 2981384 * 2 ^ 59
def prefixEnd_2981384 : Nat := 4983230072969 + 3 ^ 40 * 2981384 * 2
def baseEnd_2981384 : Nat := 1530883007624268555088871

theorem tailTrace_2981384 : CollatzResearch.WordTrace tailWord_2981384 prefixEnd_2981384 1530883007624268555088871 := by
  unfold tailWord_2981384
  simp only [CollatzResearch.WordTrace]
  refine ⟨54370003915481211347215603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72493338553974948462954137 54370003915481211347215603)
  ·
    refine ⟨81555005873221817020823405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54370003915481211347215603 81555005873221817020823405)
    ·
      refine ⟨30583127202458181382808777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81555005873221817020823405 30583127202458181382808777)
      ·
        refine ⟨22937345401843636037106583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30583127202458181382808777 22937345401843636037106583)
        ·
          refine ⟨34406018102765454055659875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22937345401843636037106583 34406018102765454055659875)
          ·
            refine ⟨51609027154148181083489813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34406018102765454055659875 51609027154148181083489813)
            ·
              refine ⟨2419173147850695988288585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51609027154148181083489813 2419173147850695988288585)
              ·
                refine ⟨1814379860888021991216439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2419173147850695988288585 1814379860888021991216439)
                ·
                  refine ⟨2721569791332032986824659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1814379860888021991216439 2721569791332032986824659)
                  ·
                    refine ⟨4082354686998049480236989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2721569791332032986824659 4082354686998049480236989)
                    ·
                      refine ⟨1530883007624268555088871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4082354686998049480236989 1530883007624268555088871)
                      ·
                        rfl

theorem cell23_2981384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_2981384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981384 prefixEnd_2981384 := by exact prefixLift 2981384
  have htrace : WordTrace (prefixWord ++ tailWord_2981384) baseStart_2981384 baseEnd_2981384 := by
    simpa [prefixWord, tailWord_2981384, baseEnd_2981384] using wordTrace_append hprefix tailTrace_2981384
  have hstable : (prefixWord ++ tailWord_2981384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981384).length < 2 ^ (prefixWord ++ tailWord_2981384).sum := by decide
  have hdescent : baseEnd_2981384 < baseStart_2981384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981393 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 3]
def baseStart_2981393 : Nat := 118140960795 + 2981393 * 2 ^ 59
def prefixEnd_2981393 : Nat := 4983230072969 + 3 ^ 40 * 2981393 * 2
def baseEnd_2981393 : Nat := 1530887628950159019876329

theorem tailTrace_2981393 : CollatzResearch.WordTrace tailWord_2981393 prefixEnd_2981393 1530887628950159019876329 := by
  unfold tailWord_2981393
  simp only [CollatzResearch.WordTrace]
  refine ⟨108740336087929817231508833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72493557391953211487672555 108740336087929817231508833)
  ·
    refine ⟨81555252065947362923631625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108740336087929817231508833 81555252065947362923631625)
    ·
      refine ⟨61166439049460522192723719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81555252065947362923631625 61166439049460522192723719)
      ·
        refine ⟨91749658574190783289085579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61166439049460522192723719 91749658574190783289085579)
        ·
          refine ⟨137624487861286174933628369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91749658574190783289085579 137624487861286174933628369)
          ·
            refine ⟨103218365895964631200221277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137624487861286174933628369 103218365895964631200221277)
            ·
              refine ⟨38706887210986736700082979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103218365895964631200221277 38706887210986736700082979)
              ·
                refine ⟨58060330816480105050124469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38706887210986736700082979 58060330816480105050124469)
                ·
                  refine ⟨5443156014045009848449169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58060330816480105050124469 5443156014045009848449169)
                  ·
                    refine ⟨4082367010533757386336877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5443156014045009848449169 4082367010533757386336877)
                    ·
                      refine ⟨1530887628950159019876329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4082367010533757386336877 1530887628950159019876329)
                      ·
                        rfl

theorem cell23_2981393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_2981393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981393 prefixEnd_2981393 := by exact prefixLift 2981393
  have htrace : WordTrace (prefixWord ++ tailWord_2981393) baseStart_2981393 baseEnd_2981393 := by
    simpa [prefixWord, tailWord_2981393, baseEnd_2981393] using wordTrace_append hprefix tailTrace_2981393
  have hstable : (prefixWord ++ tailWord_2981393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981393).length < 2 ^ (prefixWord ++ tailWord_2981393).sum := by decide
  have hdescent : baseEnd_2981393 < baseStart_2981393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981400 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 1, 6]
def baseStart_2981400 : Nat := 118140960795 + 2981400 * 2 ^ 59
def prefixEnd_2981400 : Nat := 4983230072969 + 3 ^ 40 * 2981400 * 2
def baseEnd_2981400 : Nat := 510297074438246830829599

theorem tailTrace_2981400 : CollatzResearch.WordTrace tailWord_2981400 prefixEnd_2981400 510297074438246830829599 := by
  unfold tailWord_2981400
  simp only [CollatzResearch.WordTrace]
  refine ⟨54370295699452228713506827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72493727599269638284675769 54370295699452228713506827)
  ·
    refine ⟨81555443549178343070260241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54370295699452228713506827 81555443549178343070260241)
    ·
      refine ⟨61166582661883757302695181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81555443549178343070260241 61166582661883757302695181)
      ·
        refine ⟨22937468498206408988510693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61166582661883757302695181 22937468498206408988510693)
        ·
          refine ⟨4300775343413701685345755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22937468498206408988510693 4300775343413701685345755)
          ·
            refine ⟨6451163015120552528018633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4300775343413701685345755 6451163015120552528018633)
            ·
              refine ⟨4838372261340414396013975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6451163015120552528018633 4838372261340414396013975)
              ·
                refine ⟨7257558392010621594020963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4838372261340414396013975 7257558392010621594020963)
                ·
                  refine ⟨10886337588015932391031445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7257558392010621594020963 10886337588015932391031445)
                  ·
                    refine ⟨510297074438246830829599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10886337588015932391031445 510297074438246830829599)
                    ·
                      rfl

theorem cell23_2981400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_2981400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981400 prefixEnd_2981400 := by exact prefixLift 2981400
  have htrace : WordTrace (prefixWord ++ tailWord_2981400) baseStart_2981400 baseEnd_2981400 := by
    simpa [prefixWord, tailWord_2981400, baseEnd_2981400] using wordTrace_append hprefix tailTrace_2981400
  have hstable : (prefixWord ++ tailWord_2981400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981400).length < 2 ^ (prefixWord ++ tailWord_2981400).sum := by decide
  have hdescent : baseEnd_2981400 < baseStart_2981400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981410 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_2981410 : Nat := 118140960795 + 2981410 * 2 ^ 59
def prefixEnd_2981410 : Nat := 4983230072969 + 3 ^ 40 * 2981410 * 2
def baseEnd_2981410 : Nat := 1530896358121285453363751

theorem tailTrace_2981410 : CollatzResearch.WordTrace tailWord_2981410 prefixEnd_2981410 1530896358121285453363751 := by
  unfold tailWord_2981410
  simp only [CollatzResearch.WordTrace]
  refine ⟨27185239032217057283719421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72493970752578819423251789 27185239032217057283719421)
  ·
    refine ⟨10194464637081396481394783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27185239032217057283719421 10194464637081396481394783)
    ·
      refine ⟨15291696955622094722092175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10194464637081396481394783 15291696955622094722092175)
      ·
        refine ⟨22937545433433142083138263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15291696955622094722092175 22937545433433142083138263)
        ·
          refine ⟨34406318150149713124707395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22937545433433142083138263 34406318150149713124707395)
          ·
            refine ⟨51609477225224569687061093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34406318150149713124707395 51609477225224569687061093)
            ·
              refine ⟨9676776979729606816323955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51609477225224569687061093 9676776979729606816323955)
              ·
                refine ⟨14515165469594410224485933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9676776979729606816323955 14515165469594410224485933)
                ·
                  refine ⟨5443187051097903834182225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14515165469594410224485933 5443187051097903834182225)
                  ·
                    refine ⟨4082390288323427875636669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5443187051097903834182225 4082390288323427875636669)
                    ·
                      refine ⟨1530896358121285453363751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4082390288323427875636669 1530896358121285453363751)
                      ·
                        rfl

theorem cell23_2981410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_2981410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981410 prefixEnd_2981410 := by exact prefixLift 2981410
  have htrace : WordTrace (prefixWord ++ tailWord_2981410) baseStart_2981410 baseEnd_2981410 := by
    simpa [prefixWord, tailWord_2981410, baseEnd_2981410] using wordTrace_append hprefix tailTrace_2981410
  have hstable : (prefixWord ++ tailWord_2981410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981410).length < 2 ^ (prefixWord ++ tailWord_2981410).sum := by decide
  have hdescent : baseEnd_2981410 < baseStart_2981410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981427 : List Nat := [1, 1, 1, 2, 4, 3, 4, 1, 1, 2, 3]
def baseStart_2981427 : Nat := 118140960795 + 2981427 * 2 ^ 59
def prefixEnd_2981427 : Nat := 4983230072969 + 3 ^ 40 * 2981427 * 2
def baseEnd_2981427 : Nat := 1530905087292411886851173

theorem tailTrace_2981427 : CollatzResearch.WordTrace tailWord_2981427 prefixEnd_2981427 1530905087292411886851173 := by
  unfold tailWord_2981427
  simp only [CollatzResearch.WordTrace]
  refine ⟨108741576169806641038246535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72494384113204427358831023 108741576169806641038246535)
  ·
    refine ⟨163112364254709961557369803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108741576169806641038246535 163112364254709961557369803)
    ·
      refine ⟨244668546382064942336054705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163112364254709961557369803 244668546382064942336054705)
      ·
        refine ⟨183501409786548706752041029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244668546382064942336054705 183501409786548706752041029)
        ·
          refine ⟨34406514334977882516007693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183501409786548706752041029 34406514334977882516007693)
          ·
            refine ⟨12902442875616705943502885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34406514334977882516007693 12902442875616705943502885)
            ·
              refine ⟨2419208039178132364406791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12902442875616705943502885 2419208039178132364406791)
              ·
                refine ⟨3628812058767198546610187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419208039178132364406791 3628812058767198546610187)
                ·
                  refine ⟨5443218088150797819915281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3628812058767198546610187 5443218088150797819915281)
                  ·
                    refine ⟨4082413566113098364936461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5443218088150797819915281 4082413566113098364936461)
                    ·
                      refine ⟨1530905087292411886851173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4082413566113098364936461 1530905087292411886851173)
                      ·
                        rfl

theorem cell23_2981427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 1, 2, 3].length) (baseStart_2981427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981427 prefixEnd_2981427 := by exact prefixLift 2981427
  have htrace : WordTrace (prefixWord ++ tailWord_2981427) baseStart_2981427 baseEnd_2981427 := by
    simpa [prefixWord, tailWord_2981427, baseEnd_2981427] using wordTrace_append hprefix tailTrace_2981427
  have hstable : (prefixWord ++ tailWord_2981427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981427).length < 2 ^ (prefixWord ++ tailWord_2981427).sum := by decide
  have hdescent : baseEnd_2981427 < baseStart_2981427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981430 : List Nat := [5, 1, 2, 1, 3, 1, 10]
def baseStart_2981430 : Nat := 118140960795 + 2981430 * 2 ^ 59
def prefixEnd_2981430 : Nat := 4983230072969 + 3 ^ 40 * 2981430 * 2
def baseEnd_2981430 : Nat := 18900081823881177470539

theorem tailTrace_2981430 : CollatzResearch.WordTrace tailWord_2981430 prefixEnd_2981430 18900081823881177470539 := by
  unfold tailWord_2981430
  simp only [CollatzResearch.WordTrace]
  refine ⟨6796355349299735784412859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72494457059197181700403829 6796355349299735784412859)
  ·
    refine ⟨10194533023949603676619289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6796355349299735784412859 10194533023949603676619289)
    ·
      refine ⟨7645899767962202757464467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10194533023949603676619289 7645899767962202757464467)
      ·
        refine ⟨11468849651943304136196701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7645899767962202757464467 11468849651943304136196701)
        ·
          refine ⟨4300818619478739051073763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11468849651943304136196701 4300818619478739051073763)
          ·
            refine ⟨6451227929218108576610645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4300818619478739051073763 6451227929218108576610645)
            ·
              refine ⟨18900081823881177470539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6451227929218108576610645 18900081823881177470539)
              ·
                rfl

theorem cell23_2981430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 10].length) (baseStart_2981430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981430 prefixEnd_2981430 := by exact prefixLift 2981430
  have htrace : WordTrace (prefixWord ++ tailWord_2981430) baseStart_2981430 baseEnd_2981430 := by
    simpa [prefixWord, tailWord_2981430, baseEnd_2981430] using wordTrace_append hprefix tailTrace_2981430
  have hstable : (prefixWord ++ tailWord_2981430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981430).length < 2 ^ (prefixWord ++ tailWord_2981430).sum := by decide
  have hdescent : baseEnd_2981430 < baseStart_2981430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981497 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 4, 2, 2]
def baseStart_2981497 : Nat := 118140960795 + 2981497 * 2 ^ 59
def prefixEnd_2981497 : Nat := 4983230072969 + 3 ^ 40 * 2981497 * 2
def baseEnd_2981497 : Nat := 1530941030938226612975851

theorem tailTrace_2981497 : CollatzResearch.WordTrace tailWord_2981497 prefixEnd_2981497 1530941030938226612975851 := by
  unfold tailWord_2981497
  simp only [CollatzResearch.WordTrace]
  refine ⟨108744129279553042993294745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72496086186368695328863163 108744129279553042993294745)
  ·
    refine ⟨81558096959664782244971059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108744129279553042993294745 81558096959664782244971059)
    ·
      refine ⟨122337145439497173367456589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81558096959664782244971059 122337145439497173367456589)
      ·
        refine ⟨45876429539811440012796221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122337145439497173367456589 45876429539811440012796221)
        ·
          refine ⟨17203661077429290004798583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45876429539811440012796221 17203661077429290004798583)
          ·
            refine ⟨25805491616143935007197875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17203661077429290004798583 25805491616143935007197875)
            ·
              refine ⟨38708237424215902510796813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25805491616143935007197875 38708237424215902510796813)
              ·
                refine ⟨14515589034080963441548805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38708237424215902510796813 14515589034080963441548805)
                ·
                  refine ⟨2721672943890180645290401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14515589034080963441548805 2721672943890180645290401)
                  ·
                    refine ⟨2041254707917635483967801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2721672943890180645290401 2041254707917635483967801)
                    ·
                      refine ⟨1530941030938226612975851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2041254707917635483967801 1530941030938226612975851)
                      ·
                        rfl

theorem cell23_2981497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_2981497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981497 prefixEnd_2981497 := by exact prefixLift 2981497
  have htrace : WordTrace (prefixWord ++ tailWord_2981497) baseStart_2981497 baseEnd_2981497 := by
    simpa [prefixWord, tailWord_2981497, baseEnd_2981497] using wordTrace_append hprefix tailTrace_2981497
  have hstable : (prefixWord ++ tailWord_2981497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981497).length < 2 ^ (prefixWord ++ tailWord_2981497).sum := by decide
  have hdescent : baseEnd_2981497 < baseStart_2981497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981508 : List Nat := [2, 3, 2, 1, 5, 1, 2, 1, 2, 1, 3]
def baseStart_2981508 : Nat := 118140960795 + 2981508 * 2 ^ 59
def prefixEnd_2981508 : Nat := 4983230072969 + 3 ^ 40 * 2981508 * 2
def baseEnd_2981508 : Nat := 1530946679225426069938301

theorem tailTrace_2981508 : CollatzResearch.WordTrace tailWord_2981508 prefixEnd_2981508 1530946679225426069938301 := by
  unfold tailWord_2981508
  simp only [CollatzResearch.WordTrace]
  refine ⟨54372265241256595935972589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72496353655008794581296785 54372265241256595935972589)
  ·
    refine ⟨20389599465471223475989721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54372265241256595935972589 20389599465471223475989721)
    ·
      refine ⟨15292199599103417606992291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20389599465471223475989721 15292199599103417606992291)
      ·
        refine ⟨22938299398655126410488437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15292199599103417606992291 22938299398655126410488437)
        ·
          refine ⟨2150465568623918100983291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22938299398655126410488437 2150465568623918100983291)
          ·
            refine ⟨3225698352935877151474937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150465568623918100983291 3225698352935877151474937)
            ·
              refine ⟨2419273764701907863606203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3225698352935877151474937 2419273764701907863606203)
              ·
                refine ⟨3628910647052861795409305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419273764701907863606203 3628910647052861795409305)
                ·
                  refine ⟨2721682985289646346556979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3628910647052861795409305 2721682985289646346556979)
                  ·
                    refine ⟨4082524477934469519835469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2721682985289646346556979 4082524477934469519835469)
                    ·
                      refine ⟨1530946679225426069938301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4082524477934469519835469 1530946679225426069938301)
                      ·
                        rfl

theorem cell23_2981508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_2981508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981508 prefixEnd_2981508 := by exact prefixLift 2981508
  have htrace : WordTrace (prefixWord ++ tailWord_2981508) baseStart_2981508 baseEnd_2981508 := by
    simpa [prefixWord, tailWord_2981508, baseEnd_2981508] using wordTrace_append hprefix tailTrace_2981508
  have hstable : (prefixWord ++ tailWord_2981508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981508).length < 2 ^ (prefixWord ++ tailWord_2981508).sum := by decide
  have hdescent : baseEnd_2981508 < baseStart_2981508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981573 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 1, 5, 5]
def baseStart_2981573 : Nat := 118140960795 + 2981573 * 2 ^ 59
def prefixEnd_2981573 : Nat := 4983230072969 + 3 ^ 40 * 2981573 * 2
def baseEnd_2981573 : Nat := 1530980055467968315625501

theorem tailTrace_2981573 : CollatzResearch.WordTrace tailWord_2981573 prefixEnd_2981573 1530980055467968315625501 := by
  unfold tailWord_2981573
  simp only [CollatzResearch.WordTrace]
  refine ⟨108746901227277707973061373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72497934151518471982040915 108746901227277707973061373)
  ·
    refine ⟨40780087960229140489898015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108746901227277707973061373 40780087960229140489898015)
    ·
      refine ⟨61170131940343710734847023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40780087960229140489898015 61170131940343710734847023)
      ·
        refine ⟨91755197910515566102270535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61170131940343710734847023 91755197910515566102270535)
        ·
          refine ⟨137632796865773349153405803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91755197910515566102270535 137632796865773349153405803)
          ·
            refine ⟨206449195298660023730108705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137632796865773349153405803 206449195298660023730108705)
            ·
              refine ⟨154836896473995017797581529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206449195298660023730108705 154836896473995017797581529)
              ·
                refine ⟨116127672355496263348186147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154836896473995017797581529 116127672355496263348186147)
                ·
                  refine ⟨174191508533244395022279221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116127672355496263348186147 174191508533244395022279221)
                  ·
                    refine ⟨16330453924991662033338677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 174191508533244395022279221 16330453924991662033338677)
                    ·
                      refine ⟨1530980055467968315625501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16330453924991662033338677 1530980055467968315625501)
                      ·
                        rfl

theorem cell23_2981573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_2981573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981573 prefixEnd_2981573 := by exact prefixLift 2981573
  have htrace : WordTrace (prefixWord ++ tailWord_2981573) baseStart_2981573 baseEnd_2981573 := by
    simpa [prefixWord, tailWord_2981573, baseEnd_2981573] using wordTrace_append hprefix tailTrace_2981573
  have hstable : (prefixWord ++ tailWord_2981573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981573).length < 2 ^ (prefixWord ++ tailWord_2981573).sum := by decide
  have hdescent : baseEnd_2981573 < baseStart_2981573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981583 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 6]
def baseStart_2981583 : Nat := 118140960795 + 2981583 * 2 ^ 59
def prefixEnd_2981583 : Nat := 4983230072969 + 3 ^ 40 * 2981583 * 2
def baseEnd_2981583 : Nat := 1530985190274513276500455

theorem tailTrace_2981583 : CollatzResearch.WordTrace tailWord_2981583 prefixEnd_2981583 1530985190274513276500455 := by
  unfold tailWord_2981583
  simp only [CollatzResearch.WordTrace]
  refine ⟨108747265957241479680925403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72498177304827653120616935 108747265957241479680925403)
  ·
    refine ⟨163120898935862219521388105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108747265957241479680925403 163120898935862219521388105)
    ·
      refine ⟨122340674201896664641041079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163120898935862219521388105 122340674201896664641041079)
      ·
        refine ⟨183511011302844996961561619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122340674201896664641041079 183511011302844996961561619)
        ·
          refine ⟨275266516954267495442342429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183511011302844996961561619 275266516954267495442342429)
          ·
            refine ⟨103224943857850310790878411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275266516954267495442342429 103224943857850310790878411)
            ·
              refine ⟨154837415786775466186317617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103224943857850310790878411 154837415786775466186317617)
              ·
                refine ⟨116128061840081599639738213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154837415786775466186317617 116128061840081599639738213)
                ·
                  refine ⟨21774011595015299932450915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116128061840081599639738213 21774011595015299932450915)
                  ·
                    refine ⟨32661017392522949898676373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21774011595015299932450915 32661017392522949898676373)
                    ·
                      refine ⟨1530985190274513276500455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32661017392522949898676373 1530985190274513276500455)
                      ·
                        rfl

theorem cell23_2981583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_2981583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981583 prefixEnd_2981583 := by exact prefixLift 2981583
  have htrace : WordTrace (prefixWord ++ tailWord_2981583) baseStart_2981583 baseEnd_2981583 := by
    simpa [prefixWord, tailWord_2981583, baseEnd_2981583] using wordTrace_append hprefix tailTrace_2981583
  have hstable : (prefixWord ++ tailWord_2981583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981583).length < 2 ^ (prefixWord ++ tailWord_2981583).sum := by decide
  have hdescent : baseEnd_2981583 < baseStart_2981583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981614 : List Nat := [4, 1, 2, 1, 1, 2, 1, 6, 1, 4]
def baseStart_2981614 : Nat := 118140960795 + 2981614 * 2 ^ 59
def prefixEnd_2981614 : Nat := 4983230072969 + 3 ^ 40 * 2981614 * 2
def baseEnd_2981614 : Nat := 510333702724934218404271

theorem tailTrace_2981614 : CollatzResearch.WordTrace tailWord_2981614 prefixEnd_2981614 510333702724934218404271 := by
  unfold tailWord_2981614
  simp only [CollatzResearch.WordTrace]
  refine ⟨13593549577516146496912987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72498931080086114650202597 13593549577516146496912987)
  ·
    refine ⟨20390324366274219745369481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13593549577516146496912987 20390324366274219745369481)
    ·
      refine ⟨15292743274705664809027111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20390324366274219745369481 15292743274705664809027111)
      ·
        refine ⟨22939114912058497213540667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15292743274705664809027111 22939114912058497213540667)
        ·
          refine ⟨34408672368087745820311001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22939114912058497213540667 34408672368087745820311001)
          ·
            refine ⟨25806504276065809365233251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34408672368087745820311001 25806504276065809365233251)
            ·
              refine ⟨38709756414098714047849877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25806504276065809365233251 38709756414098714047849877)
              ·
                refine ⟨1814519831910877220992963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38709756414098714047849877 1814519831910877220992963)
                ·
                  refine ⟨2721779747866315831489445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1814519831910877220992963 2721779747866315831489445)
                  ·
                    refine ⟨510333702724934218404271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2721779747866315831489445 510333702724934218404271)
                    ·
                      rfl

theorem cell23_2981614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_2981614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981614 prefixEnd_2981614 := by exact prefixLift 2981614
  have htrace : WordTrace (prefixWord ++ tailWord_2981614) baseStart_2981614 baseEnd_2981614 := by
    simpa [prefixWord, tailWord_2981614, baseEnd_2981614] using wordTrace_append hprefix tailTrace_2981614
  have hstable : (prefixWord ++ tailWord_2981614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981614).length < 2 ^ (prefixWord ++ tailWord_2981614).sum := by decide
  have hdescent : baseEnd_2981614 < baseStart_2981614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981664 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 2, 3, 2]
def baseStart_2981664 : Nat := 118140960795 + 2981664 * 2 ^ 59
def prefixEnd_2981664 : Nat := 4983230072969 + 3 ^ 40 * 2981664 * 2
def baseEnd_2981664 : Nat := 1531026782207527459587583

theorem tailTrace_2981664 : CollatzResearch.WordTrace tailWord_2981664 prefixEnd_2981664 1531026782207527459587583 := by
  unfold tailWord_2981664
  simp only [CollatzResearch.WordTrace]
  refine ⟨54375110134974015257312023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72500146846632020343082697 54375110134974015257312023)
  ·
    refine ⟨81562665202461022885968035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54375110134974015257312023 81562665202461022885968035)
    ·
      refine ⟨122343997803691534328952053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81562665202461022885968035 122343997803691534328952053)
      ·
        refine ⟨11469749794096081343339255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122343997803691534328952053 11469749794096081343339255)
        ·
          refine ⟨17204624691144122015008883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11469749794096081343339255 17204624691144122015008883)
          ·
            refine ⟨25806937036716183022513325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17204624691144122015008883 25806937036716183022513325)
            ·
              refine ⟨9677601388768568633442497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25806937036716183022513325 9677601388768568633442497)
              ·
                refine ⟨7258201041576426475081873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9677601388768568633442497 7258201041576426475081873)
                ·
                  refine ⟨5443650781182319856311405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7258201041576426475081873 5443650781182319856311405)
                  ·
                    refine ⟨2041369042943369946116777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5443650781182319856311405 2041369042943369946116777)
                    ·
                      refine ⟨1531026782207527459587583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2041369042943369946116777 1531026782207527459587583)
                      ·
                        rfl

theorem cell23_2981664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_2981664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981664 prefixEnd_2981664 := by exact prefixLift 2981664
  have htrace : WordTrace (prefixWord ++ tailWord_2981664) baseStart_2981664 baseEnd_2981664 := by
    simpa [prefixWord, tailWord_2981664, baseEnd_2981664] using wordTrace_append hprefix tailTrace_2981664
  have hstable : (prefixWord ++ tailWord_2981664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981664).length < 2 ^ (prefixWord ++ tailWord_2981664).sum := by decide
  have hdescent : baseEnd_2981664 < baseStart_2981664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981678 : List Nat := [4, 1, 3, 2, 3, 1, 2, 1, 6]
def baseStart_2981678 : Nat := 118140960795 + 2981678 * 2 ^ 59
def prefixEnd_2981678 : Nat := 4983230072969 + 3 ^ 40 * 2981678 * 2
def baseEnd_2981678 : Nat := 170114885659632267201391

theorem tailTrace_2981678 : CollatzResearch.WordTrace tailWord_2981678 prefixEnd_2981678 170114885659632267201391 := by
  unfold tailWord_2981678
  simp only [CollatzResearch.WordTrace]
  refine ⟨13593841361487163863204211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72500487261264873937089125 13593841361487163863204211)
  ·
    refine ⟨20390762042230745794806317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13593841361487163863204211 20390762042230745794806317)
    ·
      refine ⟨7646535765836529673052369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20390762042230745794806317 7646535765836529673052369)
      ·
        refine ⟨5734901824377397254789277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7646535765836529673052369 5734901824377397254789277)
        ·
          refine ⟨2150588184141523970545979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5734901824377397254789277 2150588184141523970545979)
          ·
            refine ⟨3225882276212285955818969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150588184141523970545979 3225882276212285955818969)
            ·
              refine ⟨2419411707159214466864227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3225882276212285955818969 2419411707159214466864227)
              ·
                refine ⟨3629117560738821700296341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419411707159214466864227 3629117560738821700296341)
                ·
                  refine ⟨170114885659632267201391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3629117560738821700296341 170114885659632267201391)
                  ·
                    rfl

theorem cell23_2981678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_2981678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981678 prefixEnd_2981678 := by exact prefixLift 2981678
  have htrace : WordTrace (prefixWord ++ tailWord_2981678) baseStart_2981678 baseEnd_2981678 := by
    simpa [prefixWord, tailWord_2981678, baseEnd_2981678] using wordTrace_append hprefix tailTrace_2981678
  have hstable : (prefixWord ++ tailWord_2981678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981678).length < 2 ^ (prefixWord ++ tailWord_2981678).sum := by decide
  have hdescent : baseEnd_2981678 < baseStart_2981678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981680 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 3]
def baseStart_2981680 : Nat := 118140960795 + 2981680 * 2 ^ 59
def prefixEnd_2981680 : Nat := 4983230072969 + 3 ^ 40 * 2981680 * 2
def baseEnd_2981680 : Nat := 1531034997897999396987509

theorem tailTrace_2981680 : CollatzResearch.WordTrace tailWord_2981680 prefixEnd_2981680 1531034997897999396987509 := by
  unfold tailWord_2981680
  simp only [CollatzResearch.WordTrace]
  refine ⟨54375401918945032623603247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72500535891926710164804329 54375401918945032623603247)
  ·
    refine ⟨81563102878417548935404871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54375401918945032623603247 81563102878417548935404871)
    ·
      refine ⟨122344654317626323403107307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81563102878417548935404871 122344654317626323403107307)
      ·
        refine ⟨183516981476439485104660961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122344654317626323403107307 183516981476439485104660961)
        ·
          refine ⟨137637736107329613828495721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183516981476439485104660961 137637736107329613828495721)
          ·
            refine ⟨103228302080497210371371791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137637736107329613828495721 103228302080497210371371791)
            ·
              refine ⟨154842453120745815557057687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103228302080497210371371791 154842453120745815557057687)
              ·
                refine ⟨232263679681118723335586531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154842453120745815557057687 232263679681118723335586531)
                ·
                  refine ⟨348395519521678085003379797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232263679681118723335586531 348395519521678085003379797)
                  ·
                    refine ⟨4082759994394665058633357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 348395519521678085003379797 4082759994394665058633357)
                    ·
                      refine ⟨1531034997897999396987509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4082759994394665058633357 1531034997897999396987509)
                      ·
                        rfl

theorem cell23_2981680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 3].length) (baseStart_2981680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981680 prefixEnd_2981680 := by exact prefixLift 2981680
  have htrace : WordTrace (prefixWord ++ tailWord_2981680) baseStart_2981680 baseEnd_2981680 := by
    simpa [prefixWord, tailWord_2981680, baseEnd_2981680] using wordTrace_append hprefix tailTrace_2981680
  have hstable : (prefixWord ++ tailWord_2981680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981680).length < 2 ^ (prefixWord ++ tailWord_2981680).sum := by decide
  have hdescent : baseEnd_2981680 < baseStart_2981680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981694 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_2981694 : Nat := 118140960795 + 2981694 * 2 ^ 59
def prefixEnd_2981694 : Nat := 4983230072969 + 3 ^ 40 * 2981694 * 2
def baseEnd_2981694 : Nat := 1531042186627162342212445

theorem tailTrace_2981694 : CollatzResearch.WordTrace tailWord_2981694 prefixEnd_2981694 1531042186627162342212445 := by
  unfold tailWord_2981694
  simp only [CollatzResearch.WordTrace]
  refine ⟨13593914307479918204777017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72500876306559563758810757 13593914307479918204777017)
  ·
    refine ⟨10195435730609938653582763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13593914307479918204777017 10195435730609938653582763)
    ·
      refine ⟨15293153595914907980374145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10195435730609938653582763 15293153595914907980374145)
      ·
        refine ⟨11469865196936180985280609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15293153595914907980374145 11469865196936180985280609)
        ·
          refine ⟨8602398897702135738960457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11469865196936180985280609 8602398897702135738960457)
          ·
            refine ⟨6451799173276601804220343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8602398897702135738960457 6451799173276601804220343)
            ·
              refine ⟨9677698759914902706330515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6451799173276601804220343 9677698759914902706330515)
              ·
                refine ⟨14516548139872354059495773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9677698759914902706330515 14516548139872354059495773)
                ·
                  refine ⟨5443705552452132772310915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14516548139872354059495773 5443705552452132772310915)
                  ·
                    refine ⟨8165558328678199158466373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5443705552452132772310915 8165558328678199158466373)
                    ·
                      refine ⟨1531042186627162342212445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8165558328678199158466373 1531042186627162342212445)
                      ·
                        rfl

theorem cell23_2981694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_2981694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981694 prefixEnd_2981694 := by exact prefixLift 2981694
  have htrace : WordTrace (prefixWord ++ tailWord_2981694) baseStart_2981694 baseEnd_2981694 := by
    simpa [prefixWord, tailWord_2981694, baseEnd_2981694] using wordTrace_append hprefix tailTrace_2981694
  have hstable : (prefixWord ++ tailWord_2981694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981694).length < 2 ^ (prefixWord ++ tailWord_2981694).sum := by decide
  have hdescent : baseEnd_2981694 < baseStart_2981694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981714 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_2981714 : Nat := 118140960795 + 2981714 * 2 ^ 59
def prefixEnd_2981714 : Nat := 4983230072969 + 3 ^ 40 * 2981714 * 2
def baseEnd_2981714 : Nat := 1531052456240252263962353

theorem tailTrace_2981714 : CollatzResearch.WordTrace tailWord_2981714 prefixEnd_2981714 1531052456240252263962353 := by
  unfold tailWord_2981714
  simp only [CollatzResearch.WordTrace]
  refine ⟨27188010979941722263486049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72501362613177926035962797 27188010979941722263486049)
  ·
    refine ⟨20391008234956291697614537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27188010979941722263486049 20391008234956291697614537)
    ·
      refine ⟨15293256176217218773210903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20391008234956291697614537 15293256176217218773210903)
      ·
        refine ⟨22939884264325828159816355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15293256176217218773210903 22939884264325828159816355)
        ·
          refine ⟨34409826396488742239724533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22939884264325828159816355 34409826396488742239724533)
          ·
            refine ⟨3225921224670819584974175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34409826396488742239724533 3225921224670819584974175)
            ·
              refine ⟨4838881837006229377461263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3225921224670819584974175 4838881837006229377461263)
              ·
                refine ⟨7258322755509344066191895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4838881837006229377461263 7258322755509344066191895)
                ·
                  refine ⟨10887484133264016099287843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7258322755509344066191895 10887484133264016099287843)
                  ·
                    refine ⟨16331226199896024148931765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10887484133264016099287843 16331226199896024148931765)
                    ·
                      refine ⟨1531052456240252263962353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16331226199896024148931765 1531052456240252263962353)
                      ·
                        rfl

theorem cell23_2981714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_2981714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981714 prefixEnd_2981714 := by exact prefixLift 2981714
  have htrace : WordTrace (prefixWord ++ tailWord_2981714) baseStart_2981714 baseEnd_2981714 := by
    simpa [prefixWord, tailWord_2981714, baseEnd_2981714] using wordTrace_append hprefix tailTrace_2981714
  have hstable : (prefixWord ++ tailWord_2981714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981714).length < 2 ^ (prefixWord ++ tailWord_2981714).sum := by decide
  have hdescent : baseEnd_2981714 < baseStart_2981714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981728 : List Nat := [2, 1, 1, 3, 3, 3, 1, 4, 1, 2, 2]
def baseStart_2981728 : Nat := 118140960795 + 2981728 * 2 ^ 59
def prefixEnd_2981728 : Nat := 4983230072969 + 3 ^ 40 * 2981728 * 2
def baseEnd_2981728 : Nat := 1531059644969415209187289

theorem tailTrace_2981728 : CollatzResearch.WordTrace tailWord_2981728 prefixEnd_2981728 1531059644969415209187289 := by
  unfold tailWord_2981728
  simp only [CollatzResearch.WordTrace]
  refine ⟨54376277270858084722476919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72501703027810779629969225 54376277270858084722476919)
  ·
    refine ⟨81564415906287127083715379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54376277270858084722476919 81564415906287127083715379)
    ·
      refine ⟨122346623859430690625573069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81564415906287127083715379 122346623859430690625573069)
      ·
        refine ⟨45879983947286508984589901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122346623859430690625573069 45879983947286508984589901)
        ·
          refine ⟨17204993980232440869221213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45879983947286508984589901 17204993980232440869221213)
          ·
            refine ⟨6451872742587165325957955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17204993980232440869221213 6451872742587165325957955)
            ·
              refine ⟨9677809113880747988936933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6451872742587165325957955 9677809113880747988936933)
              ·
                refine ⟨1814589208852640247925675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9677809113880747988936933 1814589208852640247925675)
                ·
                  refine ⟨2721883813278960371888513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1814589208852640247925675 2721883813278960371888513)
                  ·
                    refine ⟨2041412859959220278916385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2721883813278960371888513 2041412859959220278916385)
                    ·
                      refine ⟨1531059644969415209187289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2041412859959220278916385 1531059644969415209187289)
                      ·
                        rfl

theorem cell23_2981728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_2981728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981728 prefixEnd_2981728 := by exact prefixLift 2981728
  have htrace : WordTrace (prefixWord ++ tailWord_2981728) baseStart_2981728 baseEnd_2981728 := by
    simpa [prefixWord, tailWord_2981728, baseEnd_2981728] using wordTrace_append hprefix tailTrace_2981728
  have hstable : (prefixWord ++ tailWord_2981728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981728).length < 2 ^ (prefixWord ++ tailWord_2981728).sum := by decide
  have hdescent : baseEnd_2981728 < baseStart_2981728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981754 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2]
def baseStart_2981754 : Nat := 118140960795 + 2981754 * 2 ^ 59
def prefixEnd_2981754 : Nat := 4983230072969 + 3 ^ 40 * 2981754 * 2
def baseEnd_2981754 : Nat := 1531072995466432107462169

theorem tailTrace_2981754 : CollatzResearch.WordTrace tailWord_2981754 prefixEnd_2981754 1531072995466432107462169 := by
  unfold tailWord_2981754
  simp only [CollatzResearch.WordTrace]
  refine ⟨27188375709905493971350079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72502335226414650590266877 27188375709905493971350079)
  ·
    refine ⟨40782563564858240957025119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27188375709905493971350079 40782563564858240957025119)
    ·
      refine ⟨61173845347287361435537679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40782563564858240957025119 61173845347287361435537679)
      ·
        refine ⟨91760768020931042153306519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61173845347287361435537679 91760768020931042153306519)
        ·
          refine ⟨137641152031396563229959779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91760768020931042153306519 137641152031396563229959779)
          ·
            refine ⟨206461728047094844844939669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137641152031396563229959779 206461728047094844844939669)
            ·
              refine ⟨9677893502207570852106547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 206461728047094844844939669 9677893502207570852106547)
              ·
                refine ⟨14516840253311356278159821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9677893502207570852106547 14516840253311356278159821)
                ·
                  refine ⟨5443815094991758604309933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14516840253311356278159821 5443815094991758604309933)
                  ·
                    refine ⟨2041430660621909476616225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5443815094991758604309933 2041430660621909476616225)
                    ·
                      refine ⟨1531072995466432107462169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2041430660621909476616225 1531072995466432107462169)
                      ·
                        rfl

theorem cell23_2981754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2].length) (baseStart_2981754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981754 prefixEnd_2981754 := by exact prefixLift 2981754
  have htrace : WordTrace (prefixWord ++ tailWord_2981754) baseStart_2981754 baseEnd_2981754 := by
    simpa [prefixWord, tailWord_2981754, baseEnd_2981754] using wordTrace_append hprefix tailTrace_2981754
  have hstable : (prefixWord ++ tailWord_2981754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981754).length < 2 ^ (prefixWord ++ tailWord_2981754).sum := by decide
  have hdescent : baseEnd_2981754 < baseStart_2981754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981760 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 1, 8]
def baseStart_2981760 : Nat := 118140960795 + 2981760 * 2 ^ 59
def prefixEnd_2981760 : Nat := 4983230072969 + 3 ^ 40 * 2981760 * 2
def baseEnd_2981760 : Nat := 510358692116786361329047

theorem tailTrace_2981760 : CollatzResearch.WordTrace tailWord_2981760 prefixEnd_2981760 510358692116786361329047 := by
  unfold tailWord_2981760
  simp only [CollatzResearch.WordTrace]
  refine ⟨54376860838800119455059367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72502481118400159273412489 54376860838800119455059367)
  ·
    refine ⟨81565291258200179182589051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54376860838800119455059367 81565291258200179182589051)
    ·
      refine ⟨122347936887300268773883577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81565291258200179182589051 122347936887300268773883577)
      ·
        refine ⟨91760952665475201580412683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122347936887300268773883577 91760952665475201580412683)
        ·
          refine ⟨137641428998212802370619025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91760952665475201580412683 137641428998212802370619025)
          ·
            refine ⟨103231071748659601777964269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137641428998212802370619025 103231071748659601777964269)
            ·
              refine ⟨38711651905747350666736601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103231071748659601777964269 38711651905747350666736601)
              ·
                refine ⟨29033738929310513000052451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38711651905747350666736601 29033738929310513000052451)
                ·
                  refine ⟨43550608393965769500078677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29033738929310513000052451 43550608393965769500078677)
                  ·
                    refine ⟨510358692116786361329047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43550608393965769500078677 510358692116786361329047)
                    ·
                      rfl

theorem cell23_2981760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 8].length) (baseStart_2981760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981760 prefixEnd_2981760 := by exact prefixLift 2981760
  have htrace : WordTrace (prefixWord ++ tailWord_2981760) baseStart_2981760 baseEnd_2981760 := by
    simpa [prefixWord, tailWord_2981760, baseEnd_2981760] using wordTrace_append hprefix tailTrace_2981760
  have hstable : (prefixWord ++ tailWord_2981760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981760).length < 2 ^ (prefixWord ++ tailWord_2981760).sum := by decide
  have hdescent : baseEnd_2981760 < baseStart_2981760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981778 : List Nat := [3, 2, 3, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_2981778 : Nat := 118140960795 + 2981778 * 2 ^ 59
def prefixEnd_2981778 : Nat := 4983230072969 + 3 ^ 40 * 2981778 * 2
def baseEnd_2981778 : Nat := 1531085319002140013562059

theorem tailTrace_2981778 : CollatzResearch.WordTrace tailWord_2981778 prefixEnd_2981778 1531085319002140013562059 := by
  unfold tailWord_2981778
  simp only [CollatzResearch.WordTrace]
  refine ⟨27188594547883756996068497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72502918794356685322849325 27188594547883756996068497)
  ·
    refine ⟨20391445910912817747051373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27188594547883756996068497 20391445910912817747051373)
    ·
      refine ⟨7646792216592306655144265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20391445910912817747051373 7646792216592306655144265)
      ·
        refine ⟨5735094162444229991358199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7646792216592306655144265 5735094162444229991358199)
        ·
          refine ⟨8602641243666344987037299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5735094162444229991358199 8602641243666344987037299)
          ·
            refine ⟨12903961865499517480555949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8602641243666344987037299 12903961865499517480555949)
            ·
              refine ⟨4838985699562319055208481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12903961865499517480555949 4838985699562319055208481)
              ·
                refine ⟨3629239274671739291406361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4838985699562319055208481 3629239274671739291406361)
                ·
                  refine ⟨2721929456003804468554771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3629239274671739291406361 2721929456003804468554771)
                  ·
                    refine ⟨4082894184005706702832157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2721929456003804468554771 4082894184005706702832157)
                    ·
                      refine ⟨1531085319002140013562059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4082894184005706702832157 1531085319002140013562059)
                      ·
                        rfl

theorem cell23_2981778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_2981778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981778 prefixEnd_2981778 := by exact prefixLift 2981778
  have htrace : WordTrace (prefixWord ++ tailWord_2981778) baseStart_2981778 baseEnd_2981778 := by
    simpa [prefixWord, tailWord_2981778, baseEnd_2981778] using wordTrace_append hprefix tailTrace_2981778
  have hstable : (prefixWord ++ tailWord_2981778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981778).length < 2 ^ (prefixWord ++ tailWord_2981778).sum := by decide
  have hdescent : baseEnd_2981778 < baseStart_2981778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981847 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 5]
def baseStart_2981847 : Nat := 118140960795 + 2981847 * 2 ^ 59
def prefixEnd_2981847 : Nat := 4983230072969 + 3 ^ 40 * 2981847 * 2
def baseEnd_2981847 : Nat := 1531120749167300243599241

theorem tailTrace_2981847 : CollatzResearch.WordTrace tailWord_2981847 prefixEnd_2981847 1531120749167300243599241 := by
  unfold tailWord_2981847
  simp only [CollatzResearch.WordTrace]
  refine ⟨108756894828285052768535795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72504596552190035179023863 108756894828285052768535795)
  ·
    refine ⟨163135342242427579152803693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108756894828285052768535795 163135342242427579152803693)
    ·
      refine ⟨61175753340910342182301385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163135342242427579152803693 61175753340910342182301385)
      ·
        refine ⟨45881815005682756636726039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61175753340910342182301385 45881815005682756636726039)
        ·
          refine ⟨68822722508524134955089059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45881815005682756636726039 68822722508524134955089059)
          ·
            refine ⟨103234083762786202432633589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68822722508524134955089059 103234083762786202432633589)
            ·
              refine ⟨9678195352761206478059399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103234083762786202432633589 9678195352761206478059399)
              ·
                refine ⟨14517293029141809717089099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9678195352761206478059399 14517293029141809717089099)
                ·
                  refine ⟨21775939543712714575633649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14517293029141809717089099 21775939543712714575633649)
                  ·
                    refine ⟨16331954657784535931725237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21775939543712714575633649 16331954657784535931725237)
                    ·
                      refine ⟨1531120749167300243599241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16331954657784535931725237 1531120749167300243599241)
                      ·
                        rfl

theorem cell23_2981847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_2981847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981847 prefixEnd_2981847 := by exact prefixLift 2981847
  have htrace : WordTrace (prefixWord ++ tailWord_2981847) baseStart_2981847 baseEnd_2981847 := by
    simpa [prefixWord, tailWord_2981847, baseEnd_2981847] using wordTrace_append hprefix tailTrace_2981847
  have hstable : (prefixWord ++ tailWord_2981847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981847).length < 2 ^ (prefixWord ++ tailWord_2981847).sum := by decide
  have hdescent : baseEnd_2981847 < baseStart_2981847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981857 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_2981857 : Nat := 118140960795 + 2981857 * 2 ^ 59
def prefixEnd_2981857 : Nat := 4983230072969 + 3 ^ 40 * 2981857 * 2
def baseEnd_2981857 : Nat := 1531125883973845204474195

theorem tailTrace_2981857 : CollatzResearch.WordTrace tailWord_2981857 prefixEnd_2981857 1531125883973845204474195 := by
  unfold tailWord_2981857
  simp only [CollatzResearch.WordTrace]
  refine ⟨108757259558248824476399825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72504839705499216317599883 108757259558248824476399825)
  ·
    refine ⟨81567944668686618357299869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108757259558248824476399825 81567944668686618357299869)
    ·
      refine ⟨30587979250757481883987451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81567944668686618357299869 30587979250757481883987451)
      ·
        refine ⟨45881968876136222825981177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30587979250757481883987451 45881968876136222825981177)
        ·
          refine ⟨34411476657102167119485883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45881968876136222825981177 34411476657102167119485883)
          ·
            refine ⟨51617214985653250679228825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34411476657102167119485883 51617214985653250679228825)
            ·
              refine ⟨38712911239239938009421619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51617214985653250679228825 38712911239239938009421619)
              ·
                refine ⟨58069366858859907014132429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38712911239239938009421619 58069366858859907014132429)
                ·
                  refine ⟨21776012572072465130299661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58069366858859907014132429 21776012572072465130299661)
                  ·
                    refine ⟨8166004714527174423862373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21776012572072465130299661 8166004714527174423862373)
                    ·
                      refine ⟨1531125883973845204474195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8166004714527174423862373 1531125883973845204474195)
                      ·
                        rfl

theorem cell23_2981857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_2981857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981857 prefixEnd_2981857 := by exact prefixLift 2981857
  have htrace : WordTrace (prefixWord ++ tailWord_2981857) baseStart_2981857 baseEnd_2981857 := by
    simpa [prefixWord, tailWord_2981857, baseEnd_2981857] using wordTrace_append hprefix tailTrace_2981857
  have hstable : (prefixWord ++ tailWord_2981857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981857).length < 2 ^ (prefixWord ++ tailWord_2981857).sum := by decide
  have hdescent : baseEnd_2981857 < baseStart_2981857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981892 : List Nat := [2, 3, 2, 4, 2, 1, 2, 2, 5]
def baseStart_2981892 : Nat := 118140960795 + 2981892 * 2 ^ 59
def prefixEnd_2981892 : Nat := 4983230072969 + 3 ^ 40 * 2981892 * 2
def baseEnd_2981892 : Nat := 170127095088528063059615

theorem tailTrace_2981892 : CollatzResearch.WordTrace tailWord_2981892 prefixEnd_2981892 170127095088528063059615 := by
  unfold tailWord_2981892
  simp only [CollatzResearch.WordTrace]
  refine ⟨54379268056561012726961965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72505690742081350302615953 54379268056561012726961965)
  ·
    refine ⟨20392225521210379772610737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54379268056561012726961965 20392225521210379772610737)
    ·
      refine ⟨15294169140907784829458053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20392225521210379772610737 15294169140907784829458053)
      ·
        refine ⟨2867656713920209655523385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15294169140907784829458053 2867656713920209655523385)
        ·
          refine ⟨2150742535440157241642539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2867656713920209655523385 2150742535440157241642539)
          ·
            refine ⟨3226113803160235862463809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150742535440157241642539 3226113803160235862463809)
            ·
              refine ⟨2419585352370176896847857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3226113803160235862463809 2419585352370176896847857)
              ·
                refine ⟨1814689014277632672635893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2419585352370176896847857 1814689014277632672635893)
                ·
                  refine ⟨170127095088528063059615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1814689014277632672635893 170127095088528063059615)
                  ·
                    rfl

theorem cell23_2981892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_2981892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981892 prefixEnd_2981892 := by exact prefixLift 2981892
  have htrace : WordTrace (prefixWord ++ tailWord_2981892) baseStart_2981892 baseEnd_2981892 := by
    simpa [prefixWord, tailWord_2981892, baseEnd_2981892] using wordTrace_append hprefix tailTrace_2981892
  have hstable : (prefixWord ++ tailWord_2981892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981892).length < 2 ^ (prefixWord ++ tailWord_2981892).sum := by decide
  have hdescent : baseEnd_2981892 < baseStart_2981892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981914 : List Nat := [3, 1, 1, 3, 1, 3, 2, 3, 6]
def baseStart_2981914 : Nat := 118140960795 + 2981914 * 2 ^ 59
def prefixEnd_2981914 : Nat := 4983230072969 + 3 ^ 40 * 2981914 * 2
def baseEnd_2981914 : Nat := 170128350263461275717937

theorem tailTrace_2981914 : CollatzResearch.WordTrace tailWord_2981914 prefixEnd_2981914 170128350263461275717937 := by
  unfold tailWord_2981914
  simp only [CollatzResearch.WordTrace]
  refine ⟨27189834629760580802806199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72506225679361548807483197 27189834629760580802806199)
  ·
    refine ⟨40784751944640871204209299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27189834629760580802806199 40784751944640871204209299)
    ·
      refine ⟨61177127916961306806313949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40784751944640871204209299 61177127916961306806313949)
      ·
        refine ⟨22941422968860490052367731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61177127916961306806313949 22941422968860490052367731)
        ·
          refine ⟨34412134453290735078551597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22941422968860490052367731 34412134453290735078551597)
          ·
            refine ⟨12904550419984025654456849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34412134453290735078551597 12904550419984025654456849)
            ·
              refine ⟨9678412814988019240842637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12904550419984025654456849 9678412814988019240842637)
              ·
                refine ⟨3629404805620507215315989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9678412814988019240842637 3629404805620507215315989)
                ·
                  refine ⟨170128350263461275717937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3629404805620507215315989 170128350263461275717937)
                  ·
                    rfl

theorem cell23_2981914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 6].length) (baseStart_2981914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981914 prefixEnd_2981914 := by exact prefixLift 2981914
  have htrace : WordTrace (prefixWord ++ tailWord_2981914) baseStart_2981914 baseEnd_2981914 := by
    simpa [prefixWord, tailWord_2981914, baseEnd_2981914] using wordTrace_append hprefix tailTrace_2981914
  have hstable : (prefixWord ++ tailWord_2981914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981914).length < 2 ^ (prefixWord ++ tailWord_2981914).sum := by decide
  have hdescent : baseEnd_2981914 < baseStart_2981914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981928 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2981928 : Nat := 118140960795 + 2981928 * 2 ^ 59
def prefixEnd_2981928 : Nat := 4983230072969 + 3 ^ 40 * 2981928 * 2
def baseEnd_2981928 : Nat := 1531162341100314426686369

theorem tailTrace_2981928 : CollatzResearch.WordTrace tailWord_2981928 prefixEnd_2981928 1531162341100314426686369 := by
  unfold tailWord_2981928
  simp only [CollatzResearch.WordTrace]
  refine ⟨54379924570495801801117219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72506566093994402401489625 54379924570495801801117219)
  ·
    refine ⟨81569886855743702701675829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54379924570495801801117219 81569886855743702701675829)
    ·
      refine ⟨7647176892725972128282109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81569886855743702701675829 7647176892725972128282109)
      ·
        refine ⟨2867691334772239548105791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7647176892725972128282109 2867691334772239548105791)
        ·
          refine ⟨4301537002158359322158687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2867691334772239548105791 4301537002158359322158687)
          ·
            refine ⟨6452305503237538983238031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4301537002158359322158687 6452305503237538983238031)
            ·
              refine ⟨9678458254856308474857047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6452305503237538983238031 9678458254856308474857047)
              ·
                refine ⟨14517687382284462712285571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9678458254856308474857047 14517687382284462712285571)
                ·
                  refine ⟨21776531073426694068428357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14517687382284462712285571 21776531073426694068428357)
                  ·
                    refine ⟨4083099576267505137830317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21776531073426694068428357 4083099576267505137830317)
                    ·
                      refine ⟨1531162341100314426686369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4083099576267505137830317 1531162341100314426686369)
                      ·
                        rfl

theorem cell23_2981928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2981928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981928 prefixEnd_2981928 := by exact prefixLift 2981928
  have htrace : WordTrace (prefixWord ++ tailWord_2981928) baseStart_2981928 baseEnd_2981928 := by
    simpa [prefixWord, tailWord_2981928, baseEnd_2981928] using wordTrace_append hprefix tailTrace_2981928
  have hstable : (prefixWord ++ tailWord_2981928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981928).length < 2 ^ (prefixWord ++ tailWord_2981928).sum := by decide
  have hdescent : baseEnd_2981928 < baseStart_2981928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981951 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 2, 3, 2]
def baseStart_2981951 : Nat := 118140960795 + 2981951 * 2 ^ 59
def prefixEnd_2981951 : Nat := 4983230072969 + 3 ^ 40 * 2981951 * 2
def baseEnd_2981951 : Nat := 1531174151155367836698763

theorem tailTrace_2981951 : CollatzResearch.WordTrace tailWord_2981951 prefixEnd_2981951 1531174151155367836698763 := by
  unfold tailWord_2981951
  simp only [CollatzResearch.WordTrace]
  refine ⟨108760688019908278530321707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72507125346605519020214471 108760688019908278530321707)
  ·
    refine ⟨163141032029862417795482561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108760688019908278530321707 163141032029862417795482561)
    ·
      refine ⟨122355774022396813346611921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163141032029862417795482561 122355774022396813346611921)
      ·
        refine ⟨91766830516797610009958941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122355774022396813346611921 91766830516797610009958941)
        ·
          refine ⟨34412561443799103753734603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91766830516797610009958941 34412561443799103753734603)
          ·
            refine ⟨51618842165698655630601905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34412561443799103753734603 51618842165698655630601905)
            ·
              refine ⟨38714131624273991722951429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51618842165698655630601905 38714131624273991722951429)
              ·
                refine ⟨7258899679551373448053393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38714131624273991722951429 7258899679551373448053393)
                ·
                  refine ⟨5444174759663530086040045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7258899679551373448053393 5444174759663530086040045)
                  ·
                    refine ⟨2041565534873823782265017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5444174759663530086040045 2041565534873823782265017)
                    ·
                      refine ⟨1531174151155367836698763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2041565534873823782265017 1531174151155367836698763)
                      ·
                        rfl

theorem cell23_2981951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 3, 2].length) (baseStart_2981951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981951 prefixEnd_2981951 := by exact prefixLift 2981951
  have htrace : WordTrace (prefixWord ++ tailWord_2981951) baseStart_2981951 baseEnd_2981951 := by
    simpa [prefixWord, tailWord_2981951, baseEnd_2981951] using wordTrace_append hprefix tailTrace_2981951
  have hstable : (prefixWord ++ tailWord_2981951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981951).length < 2 ^ (prefixWord ++ tailWord_2981951).sum := by decide
  have hdescent : baseEnd_2981951 < baseStart_2981951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2981964 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 5, 1, 4]
def baseStart_2981964 : Nat := 118140960795 + 2981964 * 2 ^ 59
def prefixEnd_2981964 : Nat := 4983230072969 + 3 ^ 40 * 2981964 * 2
def baseEnd_2981964 : Nat := 1531180826403876285836203

theorem tailTrace_2981964 : CollatzResearch.WordTrace tailWord_2981964 prefixEnd_2981964 1531180826403876285836203 := by
  unfold tailWord_2981964
  simp only [CollatzResearch.WordTrace]
  refine ⟨54380581084430590875272473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72507441445907454500363297 54380581084430590875272473)
  ·
    refine ⟨40785435813322943156454355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54380581084430590875272473 40785435813322943156454355)
    ·
      refine ⟨61178153719984414734681533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40785435813322943156454355 61178153719984414734681533)
      ·
        refine ⟨22941807644994155525505575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61178153719984414734681533 22941807644994155525505575)
        ·
          refine ⟨34412711467491233288258363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22941807644994155525505575 34412711467491233288258363)
          ·
            refine ⟨51619067201236849932387545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34412711467491233288258363 51619067201236849932387545)
            ·
              refine ⟨38714300400927637449290659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51619067201236849932387545 38714300400927637449290659)
              ·
                refine ⟨58071450601391456173935989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38714300400927637449290659 58071450601391456173935989)
                ·
                  refine ⟨5444198493880449016306499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58071450601391456173935989 5444198493880449016306499)
                  ·
                    refine ⟨8166297740820673524459749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5444198493880449016306499 8166297740820673524459749)
                    ·
                      refine ⟨1531180826403876285836203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8166297740820673524459749 1531180826403876285836203)
                      ·
                        rfl

theorem cell23_2981964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_2981964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2981964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2981964 prefixEnd_2981964 := by exact prefixLift 2981964
  have htrace : WordTrace (prefixWord ++ tailWord_2981964) baseStart_2981964 baseEnd_2981964 := by
    simpa [prefixWord, tailWord_2981964, baseEnd_2981964] using wordTrace_append hprefix tailTrace_2981964
  have hstable : (prefixWord ++ tailWord_2981964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2981964).length < 2 ^ (prefixWord ++ tailWord_2981964).sum := by decide
  have hdescent : baseEnd_2981964 < baseStart_2981964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2981964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982001 : List Nat := [1, 2, 2, 2, 1, 1, 3, 5, 1, 2, 3]
def baseStart_2982001 : Nat := 118140960795 + 2982001 * 2 ^ 59
def prefixEnd_2982001 : Nat := 4983230072969 + 3 ^ 40 * 2982001 * 2
def baseEnd_2982001 : Nat := 1531199825188092641073533

theorem tailTrace_2982001 : CollatzResearch.WordTrace tailWord_2982001 prefixEnd_2982001 1531199825188092641073533 := by
  unfold tailWord_2982001
  simp only [CollatzResearch.WordTrace]
  refine ⟨108762511669727137069641857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72508341113151424713094571 108762511669727137069641857)
  ·
    refine ⟨81571883752295352802231393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108762511669727137069641857 81571883752295352802231393)
    ·
      refine ⟨61178912814221514601673545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81571883752295352802231393 61178912814221514601673545)
      ·
        refine ⟨45884184610666135951255159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61178912814221514601673545 45884184610666135951255159)
        ·
          refine ⟨68826276915999203926882739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45884184610666135951255159 68826276915999203926882739)
          ·
            refine ⟨103239415373998805890324109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68826276915999203926882739 103239415373998805890324109)
            ·
              refine ⟨38714780765249552208871541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103239415373998805890324109 38714780765249552208871541)
              ·
                refine ⟨3629510696742145519581707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38714780765249552208871541 3629510696742145519581707)
                ·
                  refine ⟨5444266045113218279372561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3629510696742145519581707 5444266045113218279372561)
                  ·
                    refine ⟨4083199533834913709529421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5444266045113218279372561 4083199533834913709529421)
                    ·
                      refine ⟨1531199825188092641073533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4083199533834913709529421 1531199825188092641073533)
                      ·
                        rfl

theorem cell23_2982001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_2982001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982001 prefixEnd_2982001 := by exact prefixLift 2982001
  have htrace : WordTrace (prefixWord ++ tailWord_2982001) baseStart_2982001 baseEnd_2982001 := by
    simpa [prefixWord, tailWord_2982001, baseEnd_2982001] using wordTrace_append hprefix tailTrace_2982001
  have hstable : (prefixWord ++ tailWord_2982001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982001).length < 2 ^ (prefixWord ++ tailWord_2982001).sum := by decide
  have hdescent : baseEnd_2982001 < baseStart_2982001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982074 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5]
def baseStart_2982074 : Nat := 118140960795 + 2982074 * 2 ^ 59
def prefixEnd_2982074 : Nat := 4983230072969 + 3 ^ 40 * 2982074 * 2
def baseEnd_2982074 : Nat := 1531237309275870855460697

theorem tailTrace_2982074 : CollatzResearch.WordTrace tailWord_2982074 prefixEnd_2982074 1531237309275870855460697 := by
  unfold tailWord_2982074
  simp only [CollatzResearch.WordTrace]
  refine ⟨27191293549615667634262319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72510116132308447024699517 27191293549615667634262319)
  ·
    refine ⟨40786940324423501451393479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27191293549615667634262319 40786940324423501451393479)
    ·
      refine ⟨61180410486635252177090219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40786940324423501451393479 61180410486635252177090219)
      ·
        refine ⟨91770615729952878265635329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61180410486635252177090219 91770615729952878265635329)
        ·
          refine ⟨68827961797464658699226497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91770615729952878265635329 68827961797464658699226497)
          ·
            refine ⟨51620971348098494024419873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68827961797464658699226497 51620971348098494024419873)
            ·
              refine ⟨38715728511073870518314905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51620971348098494024419873 38715728511073870518314905)
              ·
                refine ⟨29036796383305402888736179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38715728511073870518314905 29036796383305402888736179)
                ·
                  refine ⟨43555194574958104333104269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29036796383305402888736179 43555194574958104333104269)
                  ·
                    refine ⟨16333197965609289124914101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43555194574958104333104269 16333197965609289124914101)
                    ·
                      refine ⟨1531237309275870855460697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16333197965609289124914101 1531237309275870855460697)
                      ·
                        rfl

theorem cell23_2982074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_2982074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982074 prefixEnd_2982074 := by exact prefixLift 2982074
  have htrace : WordTrace (prefixWord ++ tailWord_2982074) baseStart_2982074 baseEnd_2982074 := by
    simpa [prefixWord, tailWord_2982074, baseEnd_2982074] using wordTrace_append hprefix tailTrace_2982074
  have hstable : (prefixWord ++ tailWord_2982074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982074).length < 2 ^ (prefixWord ++ tailWord_2982074).sum := by decide
  have hdescent : baseEnd_2982074 < baseStart_2982074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982082 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_2982082 : Nat := 118140960795 + 2982082 * 2 ^ 59
def prefixEnd_2982082 : Nat := 4983230072969 + 3 ^ 40 * 2982082 * 2
def baseEnd_2982082 : Nat := 1531241417121106824160661

theorem tailTrace_2982082 : CollatzResearch.WordTrace tailWord_2982082 prefixEnd_2982082 1531241417121106824160661 := by
  unfold tailWord_2982082
  simp only [CollatzResearch.WordTrace]
  refine ⟨27191366495608421975835125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72510310654955791935560333 27191366495608421975835125)
  ·
    refine ⟨2549190608963289560234543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27191366495608421975835125 2549190608963289560234543)
    ·
      refine ⟨3823785913444934340351815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2549190608963289560234543 3823785913444934340351815)
      ·
        refine ⟨5735678870167401510527723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3823785913444934340351815 5735678870167401510527723)
        ·
          refine ⟨8603518305251102265791585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5735678870167401510527723 8603518305251102265791585)
          ·
            refine ⟨6452638728938326699343689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8603518305251102265791585 6452638728938326699343689)
            ·
              refine ⟨4839479046703745024507767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6452638728938326699343689 4839479046703745024507767)
              ·
                refine ⟨7259218570055617536761651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4839479046703745024507767 7259218570055617536761651)
                ·
                  refine ⟨10888827855083426305142477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7259218570055617536761651 10888827855083426305142477)
                  ·
                    refine ⟨4083310445656284864428429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10888827855083426305142477 4083310445656284864428429)
                    ·
                      refine ⟨1531241417121106824160661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4083310445656284864428429 1531241417121106824160661)
                      ·
                        rfl

theorem cell23_2982082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_2982082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982082 prefixEnd_2982082 := by exact prefixLift 2982082
  have htrace : WordTrace (prefixWord ++ tailWord_2982082) baseStart_2982082 baseEnd_2982082 := by
    simpa [prefixWord, tailWord_2982082, baseEnd_2982082] using wordTrace_append hprefix tailTrace_2982082
  have hstable : (prefixWord ++ tailWord_2982082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982082).length < 2 ^ (prefixWord ++ tailWord_2982082).sum := by decide
  have hdescent : baseEnd_2982082 < baseStart_2982082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982088 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 6, 2, 2]
def baseStart_2982088 : Nat := 118140960795 + 2982088 * 2 ^ 59
def prefixEnd_2982088 : Nat := 4983230072969 + 3 ^ 40 * 2982088 * 2
def baseEnd_2982088 : Nat := 1531244498005033800685633

theorem tailTrace_2982088 : CollatzResearch.WordTrace tailWord_2982088 prefixEnd_2982088 1531244498005033800685633 := by
  unfold tailWord_2982088
  simp only [CollatzResearch.WordTrace]
  refine ⟨54382842410205975464029459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72510456546941300618705945 54382842410205975464029459)
  ·
    refine ⟨81574263615308963196044189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54382842410205975464029459 81574263615308963196044189)
    ·
      refine ⟨30590348855740861198516571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81574263615308963196044189 30590348855740861198516571)
      ·
        refine ⟨45885523283611291797774857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30590348855740861198516571 45885523283611291797774857)
        ·
          refine ⟨34414142462708468848331143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45885523283611291797774857 34414142462708468848331143)
          ·
            refine ⟨51621213694062703272496715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34414142462708468848331143 51621213694062703272496715)
            ·
              refine ⟨77431820541094054908745073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51621213694062703272496715 77431820541094054908745073)
              ·
                refine ⟨58073865405820541181558805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77431820541094054908745073 58073865405820541181558805)
                ·
                  refine ⟨2722212440897837867885569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58073865405820541181558805 2722212440897837867885569)
                  ·
                    refine ⟨2041659330673378400914177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2722212440897837867885569 2041659330673378400914177)
                    ·
                      refine ⟨1531244498005033800685633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2041659330673378400914177 1531244498005033800685633)
                      ·
                        rfl

theorem cell23_2982088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_2982088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982088 prefixEnd_2982088 := by exact prefixLift 2982088
  have htrace : WordTrace (prefixWord ++ tailWord_2982088) baseStart_2982088 baseEnd_2982088 := by
    simpa [prefixWord, tailWord_2982088, baseEnd_2982088] using wordTrace_append hprefix tailTrace_2982088
  have hstable : (prefixWord ++ tailWord_2982088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982088).length < 2 ^ (prefixWord ++ tailWord_2982088).sum := by decide
  have hdescent : baseEnd_2982088 < baseStart_2982088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982109 : List Nat := [1, 4, 3, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_2982109 : Nat := 118140960795 + 2982109 * 2 ^ 59
def prefixEnd_2982109 : Nat := 4983230072969 + 3 ^ 40 * 2982109 * 2
def baseEnd_2982109 : Nat := 1531255281098778218523037

theorem tailTrace_2982109 : CollatzResearch.WordTrace tailWord_2982109 prefixEnd_2982109 1531255281098778218523037 := by
  unfold tailWord_2982109
  simp only [CollatzResearch.WordTrace]
  refine ⟨108766450753335871514573381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72510967168890581009715587 108766450753335871514573381)
  ·
    refine ⟨20393709516250475908982509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108766450753335871514573381 20393709516250475908982509)
    ·
      refine ⟨7647641068593928465868441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20393709516250475908982509 7647641068593928465868441)
      ·
        refine ⟨5735730801445446349401331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7647641068593928465868441 5735730801445446349401331)
        ·
          refine ⟨8603596202168169524101997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5735730801445446349401331 8603596202168169524101997)
          ·
            refine ⟨3226348575813063571538249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8603596202168169524101997 3226348575813063571538249)
            ·
              refine ⟨2419761431859797678653687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3226348575813063571538249 2419761431859797678653687)
              ·
                refine ⟨3629642147789696517980531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419761431859797678653687 3629642147789696517980531)
                ·
                  refine ⟨5444463221684544776970797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3629642147789696517980531 5444463221684544776970797)
                  ·
                    refine ⟨2041673708131704291364049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5444463221684544776970797 2041673708131704291364049)
                    ·
                      refine ⟨1531255281098778218523037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2041673708131704291364049 1531255281098778218523037)
                      ·
                        rfl

theorem cell23_2982109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_2982109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982109 prefixEnd_2982109 := by exact prefixLift 2982109
  have htrace : WordTrace (prefixWord ++ tailWord_2982109) baseStart_2982109 baseEnd_2982109 := by
    simpa [prefixWord, tailWord_2982109, baseEnd_2982109] using wordTrace_append hprefix tailTrace_2982109
  have hstable : (prefixWord ++ tailWord_2982109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982109).length < 2 ^ (prefixWord ++ tailWord_2982109).sum := by decide
  have hdescent : baseEnd_2982109 < baseStart_2982109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982161 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 4]
def baseStart_2982161 : Nat := 118140960795 + 2982161 * 2 ^ 59
def prefixEnd_2982161 : Nat := 4983230072969 + 3 ^ 40 * 2982161 * 2
def baseEnd_2982161 : Nat := 1531281982092812015072797

theorem tailTrace_2982161 : CollatzResearch.WordTrace tailWord_2982161 prefixEnd_2982161 1531281982092812015072797 := by
  unfold tailWord_2982161
  simp only [CollatzResearch.WordTrace]
  refine ⟨108768347349147484395466337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72512231566098322930310891 108768347349147484395466337)
  ·
    refine ⟨81576260511860613296599753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108768347349147484395466337 81576260511860613296599753)
    ·
      refine ⟨61182195383895459972449815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81576260511860613296599753 61182195383895459972449815)
      ·
        refine ⟨91773293075843189958674723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61182195383895459972449815 91773293075843189958674723)
        ·
          refine ⟨137659939613764784938012085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91773293075843189958674723 137659939613764784938012085)
          ·
            refine ⟨12905619338790448587938633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137659939613764784938012085 12905619338790448587938633)
            ·
              refine ⟨9679214504092836440953975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12905619338790448587938633 9679214504092836440953975)
              ·
                refine ⟨14518821756139254661430963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9679214504092836440953975 14518821756139254661430963)
                ·
                  refine ⟨21778232634208881992146445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14518821756139254661430963 21778232634208881992146445)
                  ·
                    refine ⟨8166837237828330747054917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21778232634208881992146445 8166837237828330747054917)
                    ·
                      refine ⟨1531281982092812015072797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8166837237828330747054917 1531281982092812015072797)
                      ·
                        rfl

theorem cell23_2982161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_2982161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982161 prefixEnd_2982161 := by exact prefixLift 2982161
  have htrace : WordTrace (prefixWord ++ tailWord_2982161) baseStart_2982161 baseEnd_2982161 := by
    simpa [prefixWord, tailWord_2982161, baseEnd_2982161] using wordTrace_append hprefix tailTrace_2982161
  have hstable : (prefixWord ++ tailWord_2982161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982161).length < 2 ^ (prefixWord ++ tailWord_2982161).sum := by decide
  have hdescent : baseEnd_2982161 < baseStart_2982161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982171 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 5, 4]
def baseStart_2982171 : Nat := 118140960795 + 2982171 * 2 ^ 59
def prefixEnd_2982171 : Nat := 4983230072969 + 3 ^ 40 * 2982171 * 2
def baseEnd_2982171 : Nat := 510429038966452325315917

theorem tailTrace_2982171 : CollatzResearch.WordTrace tailWord_2982171 prefixEnd_2982171 510429038966452325315917 := by
  unfold tailWord_2982171
  simp only [CollatzResearch.WordTrace]
  refine ⟨108768712079111256103330367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72512474719407504068886911 108768712079111256103330367)
  ·
    refine ⟨163153068118666884154995551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108768712079111256103330367 163153068118666884154995551)
    ·
      refine ⟨244729602178000326232493327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163153068118666884154995551 244729602178000326232493327)
      ·
        refine ⟨367094403267000489348739991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244729602178000326232493327 367094403267000489348739991)
        ·
          refine ⟨550641604900500734023109987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367094403267000489348739991 550641604900500734023109987)
          ·
            refine ⟨825962407350751101034664981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550641604900500734023109987 825962407350751101034664981)
            ·
              refine ⟨38716987844566457860999921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 825962407350751101034664981 38716987844566457860999921)
              ·
                refine ⟨29037740883424843395749941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38716987844566457860999921 29037740883424843395749941)
                ·
                  refine ⟨2722288207821079068351557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29037740883424843395749941 2722288207821079068351557)
                  ·
                    refine ⟨510429038966452325315917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2722288207821079068351557 510429038966452325315917)
                    ·
                      rfl

theorem cell23_2982171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 4].length) (baseStart_2982171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982171 prefixEnd_2982171 := by exact prefixLift 2982171
  have htrace : WordTrace (prefixWord ++ tailWord_2982171) baseStart_2982171 baseEnd_2982171 := by
    simpa [prefixWord, tailWord_2982171, baseEnd_2982171] using wordTrace_append hprefix tailTrace_2982171
  have hstable : (prefixWord ++ tailWord_2982171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982171).length < 2 ^ (prefixWord ++ tailWord_2982171).sum := by decide
  have hdescent : baseEnd_2982171 < baseStart_2982171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982178 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_2982178 : Nat := 118140960795 + 2982178 * 2 ^ 59
def prefixEnd_2982178 : Nat := 4983230072969 + 3 ^ 40 * 2982178 * 2
def baseEnd_2982178 : Nat := 1531290711263938448560219

theorem tailTrace_2982178 : CollatzResearch.WordTrace tailWord_2982178 prefixEnd_2982178 1531290711263938448560219 := by
  unfold tailWord_2982178
  simp only [CollatzResearch.WordTrace]
  refine ⟨27192241847521474074708797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72512644926723930865890125 27192241847521474074708797)
  ·
    refine ⟨10197090692820552778015799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27192241847521474074708797 10197090692820552778015799)
    ·
      refine ⟨15295636039230829167023699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10197090692820552778015799 15295636039230829167023699)
      ·
        refine ⟨22943454058846243750535549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15295636039230829167023699 22943454058846243750535549)
        ·
          refine ⟨8603795272067341406450831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22943454058846243750535549 8603795272067341406450831)
          ·
            refine ⟨12905692908101012109676247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8603795272067341406450831 12905692908101012109676247)
            ·
              refine ⟨19358539362151518164514371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12905692908101012109676247 19358539362151518164514371)
              ·
                refine ⟨29037809043227277246771557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19358539362151518164514371 29037809043227277246771557)
                ·
                  refine ⟨5444589195605114483769667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29037809043227277246771557 5444589195605114483769667)
                  ·
                    refine ⟨8166883793407671725654501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5444589195605114483769667 8166883793407671725654501)
                    ·
                      refine ⟨1531290711263938448560219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8166883793407671725654501 1531290711263938448560219)
                      ·
                        rfl

theorem cell23_2982178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_2982178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982178 prefixEnd_2982178 := by exact prefixLift 2982178
  have htrace : WordTrace (prefixWord ++ tailWord_2982178) baseStart_2982178 baseEnd_2982178 := by
    simpa [prefixWord, tailWord_2982178, baseEnd_2982178] using wordTrace_append hprefix tailTrace_2982178
  have hstable : (prefixWord ++ tailWord_2982178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982178).length < 2 ^ (prefixWord ++ tailWord_2982178).sum := by decide
  have hdescent : baseEnd_2982178 < baseStart_2982178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982188 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 3, 4]
def baseStart_2982188 : Nat := 118140960795 + 2982188 * 2 ^ 59
def prefixEnd_2982188 : Nat := 4983230072969 + 3 ^ 40 * 2982188 * 2
def baseEnd_2982188 : Nat := 510431948690161136478391

theorem tailTrace_2982188 : CollatzResearch.WordTrace tailWord_2982188 prefixEnd_2982188 510431948690161136478391 := by
  unfold tailWord_2982188
  simp only [CollatzResearch.WordTrace]
  refine ⟨54384666060024834003349609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72512888080033112004466145 54384666060024834003349609)
  ·
    refine ⟨40788499545018625502512207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54384666060024834003349609 40788499545018625502512207)
    ·
      refine ⟨61182749317527938253768311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40788499545018625502512207 61182749317527938253768311)
      ·
        refine ⟨91774123976291907380652467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61182749317527938253768311 91774123976291907380652467)
        ·
          refine ⟨137661185964437861070978701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91774123976291907380652467 137661185964437861070978701)
          ·
            refine ⟨51622944736664197901617013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137661185964437861070978701 51622944736664197901617013)
            ·
              refine ⟨4839651069062268553276595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51622944736664197901617013 4839651069062268553276595)
              ·
                refine ⟨7259476603593402829914893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4839651069062268553276595 7259476603593402829914893)
                ·
                  refine ⟨2722303726347526061218085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7259476603593402829914893 2722303726347526061218085)
                  ·
                    refine ⟨510431948690161136478391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2722303726347526061218085 510431948690161136478391)
                    ·
                      rfl

theorem cell23_2982188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_2982188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982188 prefixEnd_2982188 := by exact prefixLift 2982188
  have htrace : WordTrace (prefixWord ++ tailWord_2982188) baseStart_2982188 baseEnd_2982188 := by
    simpa [prefixWord, tailWord_2982188, baseEnd_2982188] using wordTrace_append hprefix tailTrace_2982188
  have hstable : (prefixWord ++ tailWord_2982188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982188).length < 2 ^ (prefixWord ++ tailWord_2982188).sum := by decide
  have hdescent : baseEnd_2982188 < baseStart_2982188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982211 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 3]
def baseStart_2982211 : Nat := 118140960795 + 2982211 * 2 ^ 59
def prefixEnd_2982211 : Nat := 4983230072969 + 3 ^ 40 * 2982211 * 2
def baseEnd_2982211 : Nat := 1531307656125536819447567

theorem tailTrace_2982211 : CollatzResearch.WordTrace tailWord_2982211 prefixEnd_2982211 1531307656125536819447567 := by
  unfold tailWord_2982211
  simp only [CollatzResearch.WordTrace]
  refine ⟨108770170998966342934786487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72513447332644228623190991 108770170998966342934786487)
  ·
    refine ⟨163155256498449514402179731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108770170998966342934786487 163155256498449514402179731)
    ·
      refine ⟨244732884747674271603269597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163155256498449514402179731 244732884747674271603269597)
      ·
        refine ⟨91774831780377851851226099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244732884747674271603269597 91774831780377851851226099)
        ·
          refine ⟨137662247670566777776839149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91774831780377851851226099 137662247670566777776839149)
          ·
            refine ⟨51623342876462541666314681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137662247670566777776839149 51623342876462541666314681)
            ·
              refine ⟨38717507157346906249736011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51623342876462541666314681 38717507157346906249736011)
              ·
                refine ⟨58076260736020359374604017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38717507157346906249736011 58076260736020359374604017)
                ·
                  refine ⟨43557195552015269530953013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58076260736020359374604017 43557195552015269530953013)
                  ·
                    refine ⟨4083487083001431518526845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43557195552015269530953013 4083487083001431518526845)
                    ·
                      refine ⟨1531307656125536819447567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4083487083001431518526845 1531307656125536819447567)
                      ·
                        rfl

theorem cell23_2982211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_2982211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982211 prefixEnd_2982211 := by exact prefixLift 2982211
  have htrace : WordTrace (prefixWord ++ tailWord_2982211) baseStart_2982211 baseEnd_2982211 := by
    simpa [prefixWord, tailWord_2982211, baseEnd_2982211] using wordTrace_append hprefix tailTrace_2982211
  have hstable : (prefixWord ++ tailWord_2982211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982211).length < 2 ^ (prefixWord ++ tailWord_2982211).sum := by decide
  have hdescent : baseEnd_2982211 < baseStart_2982211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982212 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_2982212 : Nat := 118140960795 + 2982212 * 2 ^ 59
def prefixEnd_2982212 : Nat := 4983230072969 + 3 ^ 40 * 2982212 * 2
def baseEnd_2982212 : Nat := 1531308169606191315535063

theorem tailTrace_2982212 : CollatzResearch.WordTrace tailWord_2982212 prefixEnd_2982212 1531308169606191315535063 := by
  unfold tailWord_2982212
  simp only [CollatzResearch.WordTrace]
  refine ⟨54385103735981360052786445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72513471647975146737048593 54385103735981360052786445)
  ·
    refine ⟨20394413900993010019794917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54385103735981360052786445 20394413900993010019794917)
    ·
      refine ⟨3823952606436189378711547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20394413900993010019794917 3823952606436189378711547)
      ·
        refine ⟨5735928909654284068067321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3823952606436189378711547 5735928909654284068067321)
        ·
          refine ⟨4301946682240713051050491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5735928909654284068067321 4301946682240713051050491)
          ·
            refine ⟨6452920023361069576575737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4301946682240713051050491 6452920023361069576575737)
            ·
              refine ⟨4839690017520802182431803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6452920023361069576575737 4839690017520802182431803)
              ·
                refine ⟨7259535026281203273647705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4839690017520802182431803 7259535026281203273647705)
                ·
                  refine ⟨5444651269710902455235779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7259535026281203273647705 5444651269710902455235779)
                  ·
                    refine ⟨8166976904566353682853669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5444651269710902455235779 8166976904566353682853669)
                    ·
                      refine ⟨1531308169606191315535063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8166976904566353682853669 1531308169606191315535063)
                      ·
                        rfl

theorem cell23_2982212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_2982212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982212 prefixEnd_2982212 := by exact prefixLift 2982212
  have htrace : WordTrace (prefixWord ++ tailWord_2982212) baseStart_2982212 baseEnd_2982212 := by
    simpa [prefixWord, tailWord_2982212, baseEnd_2982212] using wordTrace_append hprefix tailTrace_2982212
  have hstable : (prefixWord ++ tailWord_2982212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982212).length < 2 ^ (prefixWord ++ tailWord_2982212).sum := by decide
  have hdescent : baseEnd_2982212 < baseStart_2982212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982248 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 3, 5]
def baseStart_2982248 : Nat := 118140960795 + 2982248 * 2 ^ 59
def prefixEnd_2982248 : Nat := 4983230072969 + 3 ^ 40 * 2982248 * 2
def baseEnd_2982248 : Nat := 510442218303251058228299

theorem tailTrace_2982248 : CollatzResearch.WordTrace tailWord_2982248 prefixEnd_2982248 510442218303251058228299 := by
  unfold tailWord_2982248
  simp only [CollatzResearch.WordTrace]
  refine ⟨54385760249916149126941699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72514346999888198835922265 54385760249916149126941699)
  ·
    refine ⟨81578640374874223690412549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54385760249916149126941699 81578640374874223690412549)
    ·
      refine ⟨15295995070288916941952353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81578640374874223690412549 15295995070288916941952353)
      ·
        refine ⟨11471996302716687706464265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15295995070288916941952353 11471996302716687706464265)
        ·
          refine ⟨8603997227037515779848199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11471996302716687706464265 8603997227037515779848199)
          ·
            refine ⟨12905995840556273669772299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8603997227037515779848199 12905995840556273669772299)
            ·
              refine ⟨19358993760834410504658449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12905995840556273669772299 19358993760834410504658449)
              ·
                refine ⟨14519245320625807878493837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19358993760834410504658449 14519245320625807878493837)
                ·
                  refine ⟨5444716995234677954435189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14519245320625807878493837 5444716995234677954435189)
                  ·
                    refine ⟨510442218303251058228299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5444716995234677954435189 510442218303251058228299)
                    ·
                      rfl

theorem cell23_2982248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_2982248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982248 prefixEnd_2982248 := by exact prefixLift 2982248
  have htrace : WordTrace (prefixWord ++ tailWord_2982248) baseStart_2982248 baseEnd_2982248 := by
    simpa [prefixWord, tailWord_2982248, baseEnd_2982248] using wordTrace_append hprefix tailTrace_2982248
  have hstable : (prefixWord ++ tailWord_2982248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982248).length < 2 ^ (prefixWord ++ tailWord_2982248).sum := by decide
  have hdescent : baseEnd_2982248 < baseStart_2982248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982268 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 1, 8, 2]
def baseStart_2982268 : Nat := 118140960795 + 2982268 * 2 ^ 59
def prefixEnd_2982268 : Nat := 4983230072969 + 3 ^ 40 * 2982268 * 2
def baseEnd_2982268 : Nat := 1531336924522843096434805

theorem tailTrace_2982268 : CollatzResearch.WordTrace tailWord_2982268 prefixEnd_2982268 1531336924522843096434805 := by
  unfold tailWord_2982268
  simp only [CollatzResearch.WordTrace]
  refine ⟨54386124979879920834805729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72514833306506561113074305 54386124979879920834805729)
  ·
    refine ⟨40789593734909940626104297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54386124979879920834805729 40789593734909940626104297)
    ·
      refine ⟨30592195301182455469578223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40789593734909940626104297 30592195301182455469578223)
      ·
        refine ⟨45888292951773683204367335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30592195301182455469578223 45888292951773683204367335)
        ·
          refine ⟨68832439427660524806551003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45888292951773683204367335 68832439427660524806551003)
          ·
            refine ⟨103248659141490787209826505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68832439427660524806551003 103248659141490787209826505)
            ·
              refine ⟨77436494356118090407369879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103248659141490787209826505 77436494356118090407369879)
              ·
                refine ⟨116154741534177135611054819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77436494356118090407369879 116154741534177135611054819)
                ·
                  refine ⟨174232112301265703416582229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116154741534177135611054819 174232112301265703416582229)
                  ·
                    refine ⟨2041782566030457461913073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 174232112301265703416582229 2041782566030457461913073)
                    ·
                      refine ⟨1531336924522843096434805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2041782566030457461913073 1531336924522843096434805)
                      ·
                        rfl

theorem cell23_2982268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_2982268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982268 prefixEnd_2982268 := by exact prefixLift 2982268
  have htrace : WordTrace (prefixWord ++ tailWord_2982268) baseStart_2982268 baseEnd_2982268 := by
    simpa [prefixWord, tailWord_2982268, baseEnd_2982268] using wordTrace_append hprefix tailTrace_2982268
  have hstable : (prefixWord ++ tailWord_2982268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982268).length < 2 ^ (prefixWord ++ tailWord_2982268).sum := by decide
  have hdescent : baseEnd_2982268 < baseStart_2982268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982271 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 5]
def baseStart_2982271 : Nat := 118140960795 + 2982271 * 2 ^ 59
def prefixEnd_2982271 : Nat := 4983230072969 + 3 ^ 40 * 2982271 * 2
def baseEnd_2982271 : Nat := 1531338464964806584697291

theorem tailTrace_2982271 : CollatzResearch.WordTrace tailWord_2982271 prefixEnd_2982271 1531338464964806584697291 := by
  unfold tailWord_2982271
  simp only [CollatzResearch.WordTrace]
  refine ⟨108772359378748973181970667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72514906252499315454647111 108772359378748973181970667)
  ·
    refine ⟨163158539068123459772956001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108772359378748973181970667 163158539068123459772956001)
    ·
      refine ⟨122368904301092594829717001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163158539068123459772956001 122368904301092594829717001)
      ·
        refine ⟨91776678225819446122287751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122368904301092594829717001 91776678225819446122287751)
        ·
          refine ⟨137665017338729169183431627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91776678225819446122287751 137665017338729169183431627)
          ·
            refine ⟨206497526008093753775147441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137665017338729169183431627 206497526008093753775147441)
            ·
              refine ⟨154873144506070315331360581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206497526008093753775147441 154873144506070315331360581)
              ·
                refine ⟨29038714594888184124630109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154873144506070315331360581 29038714594888184124630109)
                ·
                  refine ⟨10889517973083069046736291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29038714594888184124630109 10889517973083069046736291)
                  ·
                    refine ⟨16334276959624603570104437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10889517973083069046736291 16334276959624603570104437)
                    ·
                      refine ⟨1531338464964806584697291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16334276959624603570104437 1531338464964806584697291)
                      ·
                        rfl

theorem cell23_2982271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_2982271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982271 prefixEnd_2982271 := by exact prefixLift 2982271
  have htrace : WordTrace (prefixWord ++ tailWord_2982271) baseStart_2982271 baseEnd_2982271 := by
    simpa [prefixWord, tailWord_2982271, baseEnd_2982271] using wordTrace_append hprefix tailTrace_2982271
  have hstable : (prefixWord ++ tailWord_2982271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982271).length < 2 ^ (prefixWord ++ tailWord_2982271).sum := by decide
  have hdescent : baseEnd_2982271 < baseStart_2982271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982282 : List Nat := [3, 1, 2, 5, 1, 1, 1, 3, 1, 5]
def baseStart_2982282 : Nat := 118140960795 + 2982282 * 2 ^ 59
def prefixEnd_2982282 : Nat := 4983230072969 + 3 ^ 40 * 2982282 * 2
def baseEnd_2982282 : Nat := 510448037750668680553247

theorem tailTrace_2982282 : CollatzResearch.WordTrace tailWord_2982282 prefixEnd_2982282 510448037750668680553247 := by
  unfold tailWord_2982282
  simp only [CollatzResearch.WordTrace]
  refine ⟨27193190145427280515155275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72515173721139414707080733 27193190145427280515155275)
  ·
    refine ⟨40789785218140920772732913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27193190145427280515155275 40789785218140920772732913)
    ·
      refine ⟨30592338913605690579549685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40789785218140920772732913 30592338913605690579549685)
      ·
        refine ⟨2868031773150533491832783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30592338913605690579549685 2868031773150533491832783)
        ·
          refine ⟨4302047659725800237749175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2868031773150533491832783 4302047659725800237749175)
          ·
            refine ⟨6453071489588700356623763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4302047659725800237749175 6453071489588700356623763)
            ·
              refine ⟨9679607234383050534935645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6453071489588700356623763 9679607234383050534935645)
              ·
                refine ⟨3629852712893643950600867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9679607234383050534935645 3629852712893643950600867)
                ·
                  refine ⟨5444779069340465925901301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3629852712893643950600867 5444779069340465925901301)
                  ·
                    refine ⟨510448037750668680553247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5444779069340465925901301 510448037750668680553247)
                    ·
                      rfl

theorem cell23_2982282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_2982282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982282 prefixEnd_2982282 := by exact prefixLift 2982282
  have htrace : WordTrace (prefixWord ++ tailWord_2982282) baseStart_2982282 baseEnd_2982282 := by
    simpa [prefixWord, tailWord_2982282, baseEnd_2982282] using wordTrace_append hprefix tailTrace_2982282
  have hstable : (prefixWord ++ tailWord_2982282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982282).length < 2 ^ (prefixWord ++ tailWord_2982282).sum := by decide
  have hdescent : baseEnd_2982282 < baseStart_2982282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982295 : List Nat := [1, 1, 3, 3, 1, 1, 5, 2, 2, 4]
def baseStart_2982295 : Nat := 118140960795 + 2982295 * 2 ^ 59
def prefixEnd_2982295 : Nat := 4983230072969 + 3 ^ 40 * 2982295 * 2
def baseEnd_2982295 : Nat := 510450262833504830265727

theorem tailTrace_2982295 : CollatzResearch.WordTrace tailWord_2982295 prefixEnd_2982295 510450262833504830265727 := by
  unfold tailWord_2982295
  simp only [CollatzResearch.WordTrace]
  refine ⟨108773234730662025280844339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72515489820441350187229559 108773234730662025280844339)
  ·
    refine ⟨163159852095993037921266509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108773234730662025280844339 163159852095993037921266509)
    ·
      refine ⟨61184944535997389220474941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163159852095993037921266509 61184944535997389220474941)
      ·
        refine ⟨22944354200999020957678103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61184944535997389220474941 22944354200999020957678103)
        ·
          refine ⟨34416531301498531436517155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22944354200999020957678103 34416531301498531436517155)
          ·
            refine ⟨51624796952247797154775733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34416531301498531436517155 51624796952247797154775733)
            ·
              refine ⟨4839824714273230983260225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51624796952247797154775733 4839824714273230983260225)
              ·
                refine ⟨3629868535704923237445169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4839824714273230983260225 3629868535704923237445169)
                ·
                  refine ⟨2722401401778692428083877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3629868535704923237445169 2722401401778692428083877)
                  ·
                    refine ⟨510450262833504830265727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2722401401778692428083877 510450262833504830265727)
                    ·
                      rfl

theorem cell23_2982295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_2982295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982295 prefixEnd_2982295 := by exact prefixLift 2982295
  have htrace : WordTrace (prefixWord ++ tailWord_2982295) baseStart_2982295 baseEnd_2982295 := by
    simpa [prefixWord, tailWord_2982295, baseEnd_2982295] using wordTrace_append hprefix tailTrace_2982295
  have hstable : (prefixWord ++ tailWord_2982295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982295).length < 2 ^ (prefixWord ++ tailWord_2982295).sum := by decide
  have hdescent : baseEnd_2982295 < baseStart_2982295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982312 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 1, 6]
def baseStart_2982312 : Nat := 118140960795 + 2982312 * 2 ^ 59
def prefixEnd_2982312 : Nat := 4983230072969 + 3 ^ 40 * 2982312 * 2
def baseEnd_2982312 : Nat := 510453172557213641428201

theorem tailTrace_2982312 : CollatzResearch.WordTrace tailWord_2982312 prefixEnd_2982312 510453172557213641428201 := by
  unfold tailWord_2982312
  simp only [CollatzResearch.WordTrace]
  refine ⟨54386927385800218592106595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72515903181066958122808793 54386927385800218592106595)
  ·
    refine ⟨81580391078700327888159893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54386927385800218592106595 81580391078700327888159893)
    ·
      refine ⟨3824080831814077869757495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81580391078700327888159893 3824080831814077869757495)
      ·
        refine ⟨5736121247721116804636243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3824080831814077869757495 5736121247721116804636243)
        ·
          refine ⟨8604181871581675206954365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5736121247721116804636243 8604181871581675206954365)
          ·
            refine ⟨3226568201843128202607887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8604181871581675206954365 3226568201843128202607887)
            ·
              refine ⟨4839852302764692303911831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3226568201843128202607887 4839852302764692303911831)
              ·
                refine ⟨7259778454147038455867747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4839852302764692303911831 7259778454147038455867747)
                ·
                  refine ⟨10889667681220557683801621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7259778454147038455867747 10889667681220557683801621)
                  ·
                    refine ⟨510453172557213641428201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10889667681220557683801621 510453172557213641428201)
                    ·
                      rfl

theorem cell23_2982312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_2982312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982312 prefixEnd_2982312 := by exact prefixLift 2982312
  have htrace : WordTrace (prefixWord ++ tailWord_2982312) baseStart_2982312 baseEnd_2982312 := by
    simpa [prefixWord, tailWord_2982312, baseEnd_2982312] using wordTrace_append hprefix tailTrace_2982312
  have hstable : (prefixWord ++ tailWord_2982312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982312).length < 2 ^ (prefixWord ++ tailWord_2982312).sum := by decide
  have hdescent : baseEnd_2982312 < baseStart_2982312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982341 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 8]
def baseStart_2982341 : Nat := 118140960795 + 2982341 * 2 ^ 59
def prefixEnd_2982341 : Nat := 4983230072969 + 3 ^ 40 * 2982341 * 2
def baseEnd_2982341 : Nat := 1531374408610621310821969

theorem tailTrace_2982341 : CollatzResearch.WordTrace tailWord_2982341 prefixEnd_2982341 1531374408610621310821969 := by
  unfold tailWord_2982341
  simp only [CollatzResearch.WordTrace]
  refine ⟨108774912488495375137018877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72516608325663583424679251 108774912488495375137018877)
  ·
    refine ⟨40790592183185765676382079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108774912488495375137018877 40790592183185765676382079)
    ·
      refine ⟨61185888274778648514573119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40790592183185765676382079 61185888274778648514573119)
      ·
        refine ⟨91778832412167972771859679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61185888274778648514573119 91778832412167972771859679)
        ·
          refine ⟨137668248618251959157789519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91778832412167972771859679 137668248618251959157789519)
          ·
            refine ⟨206502372927377938736684279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137668248618251959157789519 206502372927377938736684279)
            ·
              refine ⟨309753559391066908105026419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206502372927377938736684279 309753559391066908105026419)
              ·
                refine ⟨464630339086600362157539629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309753559391066908105026419 464630339086600362157539629)
                ·
                  refine ⟨174236377157475135809077361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464630339086600362157539629 174236377157475135809077361)
                  ·
                    refine ⟨130677282868106351856808021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 174236377157475135809077361 130677282868106351856808021)
                    ·
                      refine ⟨1531374408610621310821969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 130677282868106351856808021 1531374408610621310821969)
                      ·
                        rfl

theorem cell23_2982341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_2982341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982341 prefixEnd_2982341 := by exact prefixLift 2982341
  have htrace : WordTrace (prefixWord ++ tailWord_2982341) baseStart_2982341 baseEnd_2982341 := by
    simpa [prefixWord, tailWord_2982341, baseEnd_2982341] using wordTrace_append hprefix tailTrace_2982341
  have hstable : (prefixWord ++ tailWord_2982341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982341).length < 2 ^ (prefixWord ++ tailWord_2982341).sum := by decide
  have hdescent : baseEnd_2982341 < baseStart_2982341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982475 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 3, 4]
def baseStart_2982475 : Nat := 118140960795 + 2982475 * 2 ^ 59
def prefixEnd_2982475 : Nat := 4983230072969 + 3 ^ 40 * 2982475 * 2
def baseEnd_2982475 : Nat := 510481071672774595515451

theorem tailTrace_2982475 : CollatzResearch.WordTrace tailWord_2982475 prefixEnd_2982475 510481071672774595515451 := by
  unfold tailWord_2982475
  simp only [CollatzResearch.WordTrace]
  refine ⟨108779799870009916022396879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72519866580006610681597919 108779799870009916022396879)
  ·
    refine ⟨163169699805014874033595319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108779799870009916022396879 163169699805014874033595319)
    ·
      refine ⟨244754549707522311050392979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163169699805014874033595319 244754549707522311050392979)
      ·
        refine ⟨367131824561283466575589469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244754549707522311050392979 367131824561283466575589469)
        ·
          refine ⟨137674434210481299965846051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367131824561283466575589469 137674434210481299965846051)
          ·
            refine ⟨206511651315721949948769077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137674434210481299965846051 206511651315721949948769077)
            ·
              refine ⟨19360467310848932807697101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 206511651315721949948769077 19360467310848932807697101)
              ·
                refine ⟨7260175241568349802886413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19360467310848932807697101 7260175241568349802886413)
                ·
                  refine ⟨2722565715588131176082405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7260175241568349802886413 2722565715588131176082405)
                  ·
                    refine ⟨510481071672774595515451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2722565715588131176082405 510481071672774595515451)
                    ·
                      rfl

theorem cell23_2982475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 4].length) (baseStart_2982475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982475 prefixEnd_2982475 := by exact prefixLift 2982475
  have htrace : WordTrace (prefixWord ++ tailWord_2982475) baseStart_2982475 baseEnd_2982475 := by
    simpa [prefixWord, tailWord_2982475, baseEnd_2982475] using wordTrace_append hprefix tailTrace_2982475
  have hstable : (prefixWord ++ tailWord_2982475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982475).length < 2 ^ (prefixWord ++ tailWord_2982475).sum := by decide
  have hdescent : baseEnd_2982475 < baseStart_2982475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982482 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 2, 4, 2]
def baseStart_2982482 : Nat := 118140960795 + 2982482 * 2 ^ 59
def prefixEnd_2982482 : Nat := 4983230072969 + 3 ^ 40 * 2982482 * 2
def baseEnd_2982482 : Nat := 1531446809382905259158821

theorem tailTrace_2982482 : CollatzResearch.WordTrace tailWord_2982482 prefixEnd_2982482 1531446809382905259158821 := by
  unfold tailWord_2982482
  simp only [CollatzResearch.WordTrace]
  refine ⟨27195013795246139054475425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72520036787323037478601133 27195013795246139054475425)
  ·
    refine ⟨20396260346434604290856569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27195013795246139054475425 20396260346434604290856569)
    ·
      refine ⟨15297195259825953218142427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20396260346434604290856569 15297195259825953218142427)
      ·
        refine ⟨22945792889738929827213641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15297195259825953218142427 22945792889738929827213641)
        ·
          refine ⟨17209344667304197370410231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22945792889738929827213641 17209344667304197370410231)
          ·
            refine ⟨25814017000956296055615347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17209344667304197370410231 25814017000956296055615347)
            ·
              refine ⟨38721025501434444083423021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25814017000956296055615347 38721025501434444083423021)
              ·
                refine ⟨14520384563037916531283633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38721025501434444083423021 14520384563037916531283633)
                ·
                  refine ⟨10890288422278437398462725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14520384563037916531283633 10890288422278437398462725)
                  ·
                    refine ⟨2041929079177207012211761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10890288422278437398462725 2041929079177207012211761)
                    ·
                      refine ⟨1531446809382905259158821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2041929079177207012211761 1531446809382905259158821)
                      ·
                        rfl

theorem cell23_2982482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_2982482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982482 prefixEnd_2982482 := by exact prefixLift 2982482
  have htrace : WordTrace (prefixWord ++ tailWord_2982482) baseStart_2982482 baseEnd_2982482 := by
    simpa [prefixWord, tailWord_2982482, baseEnd_2982482] using wordTrace_append hprefix tailTrace_2982482
  have hstable : (prefixWord ++ tailWord_2982482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982482).length < 2 ^ (prefixWord ++ tailWord_2982482).sum := by decide
  have hdescent : baseEnd_2982482 < baseStart_2982482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982485 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 1, 4, 3]
def baseStart_2982485 : Nat := 118140960795 + 2982485 * 2 ^ 59
def prefixEnd_2982485 : Nat := 4983230072969 + 3 ^ 40 * 2982485 * 2
def baseEnd_2982485 : Nat := 1531448349824868747421307

theorem tailTrace_2982485 : CollatzResearch.WordTrace tailWord_2982485 prefixEnd_2982485 1531448349824868747421307 := by
  unfold tailWord_2982485
  simp only [CollatzResearch.WordTrace]
  refine ⟨108780164599973687730260909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72520109733315791820173939 108780164599973687730260909)
  ·
    refine ⟨40792561724990132898847841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108780164599973687730260909 40792561724990132898847841)
    ·
      refine ⟨30594421293742599674135881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40792561724990132898847841 30594421293742599674135881)
      ·
        refine ⟨22945815970306949755601911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30594421293742599674135881 22945815970306949755601911)
        ·
          refine ⟨34418723955460424633402867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22945815970306949755601911 34418723955460424633402867)
          ·
            refine ⟨51628085933190636950104301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34418723955460424633402867 51628085933190636950104301)
            ·
              refine ⟨19360532224946488856289113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51628085933190636950104301 19360532224946488856289113)
              ·
                refine ⟨14520399168709866642216835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19360532224946488856289113 14520399168709866642216835)
                ·
                  refine ⟨21780598753064799963325253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14520399168709866642216835 21780598753064799963325253)
                  ·
                    refine ⟨4083862266199649993123485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21780598753064799963325253 4083862266199649993123485)
                    ·
                      refine ⟨1531448349824868747421307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4083862266199649993123485 1531448349824868747421307)
                      ·
                        rfl

theorem cell23_2982485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_2982485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982485 prefixEnd_2982485 := by exact prefixLift 2982485
  have htrace : WordTrace (prefixWord ++ tailWord_2982485) baseStart_2982485 baseEnd_2982485 := by
    simpa [prefixWord, tailWord_2982485, baseEnd_2982485] using wordTrace_append hprefix tailTrace_2982485
  have hstable : (prefixWord ++ tailWord_2982485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982485).length < 2 ^ (prefixWord ++ tailWord_2982485).sum := by decide
  have hdescent : baseEnd_2982485 < baseStart_2982485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982535 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 3, 5]
def baseStart_2982535 : Nat := 118140960795 + 2982535 * 2 ^ 59
def prefixEnd_2982535 : Nat := 4983230072969 + 3 ^ 40 * 2982535 * 2
def baseEnd_2982535 : Nat := 510491341285864517265359

theorem tailTrace_2982535 : CollatzResearch.WordTrace tailWord_2982535 prefixEnd_2982535 510491341285864517265359 := by
  unfold tailWord_2982535
  simp only [CollatzResearch.WordTrace]
  refine ⟨108781988249792546269581059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72521325499861697513054039 108781988249792546269581059)
  ·
    refine ⟨163172982374688819404371589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108781988249792546269581059 163172982374688819404371589)
    ·
      refine ⟨30594934195254153638319673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163172982374688819404371589 30594934195254153638319673)
      ·
        refine ⟨22946200646440615228739755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30594934195254153638319673 22946200646440615228739755)
        ·
          refine ⟨34419300969660922843109633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22946200646440615228739755 34419300969660922843109633)
          ·
            refine ⟨25814475727245692132332225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34419300969660922843109633 25814475727245692132332225)
            ·
              refine ⟨19360856795434269099249169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25814475727245692132332225 19360856795434269099249169)
              ·
                refine ⟨14520642596575701824436877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19360856795434269099249169 14520642596575701824436877)
                ·
                  refine ⟨5445240973715888184163829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14520642596575701824436877 5445240973715888184163829)
                  ·
                    refine ⟨510491341285864517265359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5445240973715888184163829 510491341285864517265359)
                    ·
                      rfl

theorem cell23_2982535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_2982535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982535 prefixEnd_2982535 := by exact prefixLift 2982535
  have htrace : WordTrace (prefixWord ++ tailWord_2982535) baseStart_2982535 baseEnd_2982535 := by
    simpa [prefixWord, tailWord_2982535, baseEnd_2982535] using wordTrace_append hprefix tailTrace_2982535
  have hstable : (prefixWord ++ tailWord_2982535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982535).length < 2 ^ (prefixWord ++ tailWord_2982535).sum := by decide
  have hdescent : baseEnd_2982535 < baseStart_2982535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982585 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 5, 2, 4]
def baseStart_2982585 : Nat := 118140960795 + 2982585 * 2 ^ 59
def prefixEnd_2982585 : Nat := 4983230072969 + 3 ^ 40 * 2982585 * 2
def baseEnd_2982585 : Nat := 1531499697890318356170847

theorem tailTrace_2982585 : CollatzResearch.WordTrace tailWord_2982585 prefixEnd_2982585 1531499697890318356170847 := by
  unfold tailWord_2982585
  simp only [CollatzResearch.WordTrace]
  refine ⟨108783811899611404808901209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72522541266407603205934139 108783811899611404808901209)
  ·
    refine ⟨81587858924708553606675907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108783811899611404808901209 81587858924708553606675907)
    ·
      refine ⟨122381788387062830410013861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81587858924708553606675907 122381788387062830410013861)
      ·
        refine ⟨22946585322574280701877599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122381788387062830410013861 22946585322574280701877599)
        ·
          refine ⟨34419877983861421052816399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22946585322574280701877599 34419877983861421052816399)
          ·
            refine ⟨51629816975792131579224599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34419877983861421052816399 51629816975792131579224599)
            ·
              refine ⟨77444725463688197368836899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51629816975792131579224599 77444725463688197368836899)
              ·
                refine ⟨116167088195532296053255349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77444725463688197368836899 116167088195532296053255349)
                ·
                  refine ⟨10890664518331152754992689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116167088195532296053255349 10890664518331152754992689)
                  ·
                    refine ⟨8167998388748364566244517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10890664518331152754992689 8167998388748364566244517)
                    ·
                      refine ⟨1531499697890318356170847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8167998388748364566244517 1531499697890318356170847)
                      ·
                        rfl

theorem cell23_2982585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_2982585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982585 prefixEnd_2982585 := by exact prefixLift 2982585
  have htrace : WordTrace (prefixWord ++ tailWord_2982585) baseStart_2982585 baseEnd_2982585 := by
    simpa [prefixWord, tailWord_2982585, baseEnd_2982585] using wordTrace_append hprefix tailTrace_2982585
  have hstable : (prefixWord ++ tailWord_2982585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982585).length < 2 ^ (prefixWord ++ tailWord_2982585).sum := by decide
  have hdescent : baseEnd_2982585 < baseStart_2982585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982592 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 3]
def baseStart_2982592 : Nat := 118140960795 + 2982592 * 2 ^ 59
def prefixEnd_2982592 : Nat := 4983230072969 + 3 ^ 40 * 2982592 * 2
def baseEnd_2982592 : Nat := 1531503292254899828783315

theorem tailTrace_2982592 : CollatzResearch.WordTrace tailWord_2982592 prefixEnd_2982592 1531503292254899828783315 := by
  unfold tailWord_2982592
  simp only [CollatzResearch.WordTrace]
  refine ⟨54392033605293022502203015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72522711473724030002937353 54392033605293022502203015)
  ·
    refine ⟨81588050407939533753304523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54392033605293022502203015 81588050407939533753304523)
    ·
      refine ⟨122382075611909300629956785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81588050407939533753304523 122382075611909300629956785)
      ·
        refine ⟨91786556708931975472467589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122382075611909300629956785 91786556708931975472467589)
        ·
          refine ⟨17209979382924745401087673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91786556708931975472467589 17209979382924745401087673)
          ·
            refine ⟨12907484537193559050815755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17209979382924745401087673 12907484537193559050815755)
            ·
              refine ⟨19361226805790338576223633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12907484537193559050815755 19361226805790338576223633)
              ·
                refine ⟨14520920104342753932167725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19361226805790338576223633 14520920104342753932167725)
                ·
                  refine ⟨5445345039128532724562897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14520920104342753932167725 5445345039128532724562897)
                  ·
                    refine ⟨4084008779346399543422173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5445345039128532724562897 4084008779346399543422173)
                    ·
                      refine ⟨1531503292254899828783315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4084008779346399543422173 1531503292254899828783315)
                      ·
                        rfl

theorem cell23_2982592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_2982592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982592 prefixEnd_2982592 := by exact prefixLift 2982592
  have htrace : WordTrace (prefixWord ++ tailWord_2982592) baseStart_2982592 baseEnd_2982592 := by
    simpa [prefixWord, tailWord_2982592, baseEnd_2982592] using wordTrace_append hprefix tailTrace_2982592
  have hstable : (prefixWord ++ tailWord_2982592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982592).length < 2 ^ (prefixWord ++ tailWord_2982592).sum := by decide
  have hdescent : baseEnd_2982592 < baseStart_2982592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982602 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_2982602 : Nat := 118140960795 + 2982602 * 2 ^ 59
def prefixEnd_2982602 : Nat := 4983230072969 + 3 ^ 40 * 2982602 * 2
def baseEnd_2982602 : Nat := 1531508427061444789658269

theorem tailTrace_2982602 : CollatzResearch.WordTrace tailWord_2982602 prefixEnd_2982602 1531508427061444789658269 := by
  unfold tailWord_2982602
  simp only [CollatzResearch.WordTrace]
  refine ⟨27196107985137454178067515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72522954627033211141513373 27196107985137454178067515)
  ·
    refine ⟨40794161977706181267101273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27196107985137454178067515 40794161977706181267101273)
    ·
      refine ⟨30595621483279635950325955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40794161977706181267101273 30595621483279635950325955)
      ·
        refine ⟨45893432224919453925488933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30595621483279635950325955 45893432224919453925488933)
        ·
          refine ⟨8605018542172397611029175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45893432224919453925488933 8605018542172397611029175)
          ·
            refine ⟨12907527813258596416543763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8605018542172397611029175 12907527813258596416543763)
            ·
              refine ⟨19361291719887894624815645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12907527813258596416543763 19361291719887894624815645)
              ·
                refine ⟨7260484394957960484305867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19361291719887894624815645 7260484394957960484305867)
                ·
                  refine ⟨10890726592436940726458801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7260484394957960484305867 10890726592436940726458801)
                  ·
                    refine ⟨8168044944327705544844101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10890726592436940726458801 8168044944327705544844101)
                    ·
                      refine ⟨1531508427061444789658269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8168044944327705544844101 1531508427061444789658269)
                      ·
                        rfl

theorem cell23_2982602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_2982602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982602 prefixEnd_2982602 := by exact prefixLift 2982602
  have htrace : WordTrace (prefixWord ++ tailWord_2982602) baseStart_2982602 baseEnd_2982602 := by
    simpa [prefixWord, tailWord_2982602, baseEnd_2982602] using wordTrace_append hprefix tailTrace_2982602
  have hstable : (prefixWord ++ tailWord_2982602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982602).length < 2 ^ (prefixWord ++ tailWord_2982602).sum := by decide
  have hdescent : baseEnd_2982602 < baseStart_2982602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982606 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2]
def baseStart_2982606 : Nat := 118140960795 + 2982606 * 2 ^ 59
def prefixEnd_2982606 : Nat := 4983230072969 + 3 ^ 40 * 2982606 * 2
def baseEnd_2982606 : Nat := 1531510480984062774008251

theorem tailTrace_2982606 : CollatzResearch.WordTrace tailWord_2982606 prefixEnd_2982606 1531510480984062774008251 := by
  unfold tailWord_2982606
  simp only [CollatzResearch.WordTrace]
  refine ⟨13598072229066915674426959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72523051888356883596943781 13598072229066915674426959)
  ·
    refine ⟨20397108343600373511640439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13598072229066915674426959 20397108343600373511640439)
    ·
      refine ⟨30595662515400560267460659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20397108343600373511640439 30595662515400560267460659)
      ·
        refine ⟨45893493773100840401190989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30595662515400560267460659 45893493773100840401190989)
        ·
          refine ⟨17210060164912815150446621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45893493773100840401190989 17210060164912815150446621)
          ·
            refine ⟨6453772561842305681417483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17210060164912815150446621 6453772561842305681417483)
            ·
              refine ⟨9680658842763458522126225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6453772561842305681417483 9680658842763458522126225)
              ·
                refine ⟨7260494132072593891594669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9680658842763458522126225 7260494132072593891594669)
                ·
                  refine ⟨2722685299527222709348001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7260494132072593891594669 2722685299527222709348001)
                  ·
                    refine ⟨2042013974645417032011001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2722685299527222709348001 2042013974645417032011001)
                    ·
                      refine ⟨1531510480984062774008251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2042013974645417032011001 1531510480984062774008251)
                      ·
                        rfl

theorem cell23_2982606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_2982606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982606 prefixEnd_2982606 := by exact prefixLift 2982606
  have htrace : WordTrace (prefixWord ++ tailWord_2982606) baseStart_2982606 baseEnd_2982606 := by
    simpa [prefixWord, tailWord_2982606, baseEnd_2982606] using wordTrace_append hprefix tailTrace_2982606
  have hstable : (prefixWord ++ tailWord_2982606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982606).length < 2 ^ (prefixWord ++ tailWord_2982606).sum := by decide
  have hdescent : baseEnd_2982606 < baseStart_2982606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982623 : List Nat := [1, 1, 2, 3, 2, 4, 2, 3, 1, 2, 2]
def baseStart_2982623 : Nat := 118140960795 + 2982623 * 2 ^ 59
def prefixEnd_2982623 : Nat := 4983230072969 + 3 ^ 40 * 2982623 * 2
def baseEnd_2982623 : Nat := 1531519210155189207495673

theorem tailTrace_2982623 : CollatzResearch.WordTrace tailWord_2982623 prefixEnd_2982623 1531519210155189207495673 := by
  unfold tailWord_2982623
  simp only [CollatzResearch.WordTrace]
  refine ⟨108785197873473737298784523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72523465248982491532523015 108785197873473737298784523)
  ·
    refine ⟨163177796810210605948176785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108785197873473737298784523 163177796810210605948176785)
    ·
      refine ⟨122383347607657954461132589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163177796810210605948176785 122383347607657954461132589)
      ·
        refine ⟨45893755352871732922924721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122383347607657954461132589 45893755352871732922924721)
        ·
          refine ⟨34420316514653799692193541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45893755352871732922924721 34420316514653799692193541)
          ·
            refine ⟨6453809346497587442286289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34420316514653799692193541 6453809346497587442286289)
            ·
              refine ⟨4840357009873190581714717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6453809346497587442286289 4840357009873190581714717)
              ·
                refine ⟨1815133878702446468143019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4840357009873190581714717 1815133878702446468143019)
                ·
                  refine ⟨2722700818053669702214529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1815133878702446468143019 2722700818053669702214529)
                  ·
                    refine ⟨2042025613540252276660897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2722700818053669702214529 2042025613540252276660897)
                    ·
                      refine ⟨1531519210155189207495673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2042025613540252276660897 1531519210155189207495673)
                      ·
                        rfl

theorem cell23_2982623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_2982623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982623 prefixEnd_2982623 := by exact prefixLift 2982623
  have htrace : WordTrace (prefixWord ++ tailWord_2982623) baseStart_2982623 baseEnd_2982623 := by
    simpa [prefixWord, tailWord_2982623, baseEnd_2982623] using wordTrace_append hprefix tailTrace_2982623
  have hstable : (prefixWord ++ tailWord_2982623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982623).length < 2 ^ (prefixWord ++ tailWord_2982623).sum := by decide
  have hdescent : baseEnd_2982623 < baseStart_2982623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982639 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 4, 1, 3]
def baseStart_2982639 : Nat := 118140960795 + 2982639 * 2 ^ 59
def prefixEnd_2982639 : Nat := 4983230072969 + 3 ^ 40 * 2982639 * 2
def baseEnd_2982639 : Nat := 1531527425845661144895599

theorem tailTrace_2982639 : CollatzResearch.WordTrace tailWord_2982639 prefixEnd_2982639 1531527425845661144895599 := by
  unfold tailWord_2982639
  simp only [CollatzResearch.WordTrace]
  refine ⟨108785781441415772031366971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72523854294277181354244647 108785781441415772031366971)
  ·
    refine ⟨163178672162123658047050457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108785781441415772031366971 163178672162123658047050457)
    ·
      refine ⟨122384004121592743535287843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163178672162123658047050457 122384004121592743535287843)
      ·
        refine ⟨183576006182389115302931765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122384004121592743535287843 183576006182389115302931765)
        ·
          refine ⟨17210250579598979559649853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183576006182389115302931765 17210250579598979559649853)
          ·
            refine ⟨6453843967349617334868695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17210250579598979559649853 6453843967349617334868695)
            ·
              refine ⟨9680765951024426002303043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6453843967349617334868695 9680765951024426002303043)
              ·
                refine ⟨14521148926536639003454565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9680765951024426002303043 14521148926536639003454565)
                ·
                  refine ⟨2722715423725619813147731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14521148926536639003454565 2722715423725619813147731)
                  ·
                    refine ⟨4084073135588429719721597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2722715423725619813147731 4084073135588429719721597)
                    ·
                      refine ⟨1531527425845661144895599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4084073135588429719721597 1531527425845661144895599)
                      ·
                        rfl

theorem cell23_2982639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 1, 3].length) (baseStart_2982639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982639 prefixEnd_2982639 := by exact prefixLift 2982639
  have htrace : WordTrace (prefixWord ++ tailWord_2982639) baseStart_2982639 baseEnd_2982639 := by
    simpa [prefixWord, tailWord_2982639, baseEnd_2982639] using wordTrace_append hprefix tailTrace_2982639
  have hstable : (prefixWord ++ tailWord_2982639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982639).length < 2 ^ (prefixWord ++ tailWord_2982639).sum := by decide
  have hdescent : baseEnd_2982639 < baseStart_2982639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982666 : List Nat := [3, 1, 2, 2, 1, 2, 4, 2, 1, 3, 2]
def baseStart_2982666 : Nat := 118140960795 + 2982666 * 2 ^ 59
def prefixEnd_2982666 : Nat := 4983230072969 + 3 ^ 40 * 2982666 * 2
def baseEnd_2982666 : Nat := 1531541289823332539257975

theorem tailTrace_2982666 : CollatzResearch.WordTrace tailWord_2982666 prefixEnd_2982666 1531541289823332539257975 := by
  unfold tailWord_2982666
  simp only [CollatzResearch.WordTrace]
  refine ⟨27196691553079488910649963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72524510808211970428399901 27196691553079488910649963)
  ·
    refine ⟨40795037329619233365974945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27196691553079488910649963 40795037329619233365974945)
    ·
      refine ⟨30596277997214425024481209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40795037329619233365974945 30596277997214425024481209)
      ·
        refine ⟨22947208497910818768360907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30596277997214425024481209 22947208497910818768360907)
        ·
          refine ⟨34420812746866228152541361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22947208497910818768360907 34420812746866228152541361)
          ·
            refine ⟨25815609560149671114406021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34420812746866228152541361 25815609560149671114406021)
            ·
              refine ⟨4840426792528063333951129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25815609560149671114406021 4840426792528063333951129)
              ·
                refine ⟨3630320094396047500463347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4840426792528063333951129 3630320094396047500463347)
                ·
                  refine ⟨5445480141594071250695021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3630320094396047500463347 5445480141594071250695021)
                  ·
                    refine ⟨2042055053097776719010633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5445480141594071250695021 2042055053097776719010633)
                    ·
                      refine ⟨1531541289823332539257975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2042055053097776719010633 1531541289823332539257975)
                      ·
                        rfl

theorem cell23_2982666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_2982666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982666 prefixEnd_2982666 := by exact prefixLift 2982666
  have htrace : WordTrace (prefixWord ++ tailWord_2982666) baseStart_2982666 baseEnd_2982666 := by
    simpa [prefixWord, tailWord_2982666, baseEnd_2982666] using wordTrace_append hprefix tailTrace_2982666
  have hstable : (prefixWord ++ tailWord_2982666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982666).length < 2 ^ (prefixWord ++ tailWord_2982666).sum := by decide
  have hdescent : baseEnd_2982666 < baseStart_2982666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982674 : List Nat := [3, 2, 4, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_2982674 : Nat := 118140960795 + 2982674 * 2 ^ 59
def prefixEnd_2982674 : Nat := 4983230072969 + 3 ^ 40 * 2982674 * 2
def baseEnd_2982674 : Nat := 1531545397668568507957939

theorem tailTrace_2982674 : CollatzResearch.WordTrace tailWord_2982674 prefixEnd_2982674 1531545397668568507957939 := by
  unfold tailWord_2982674
  simp only [CollatzResearch.WordTrace]
  refine ⟨27196764499072243252222769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72524705330859315339260717 27196764499072243252222769)
  ·
    refine ⟨20397573374304182439167077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27196764499072243252222769 20397573374304182439167077)
    ·
      refine ⟨3824545007682034207343827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20397573374304182439167077 3824545007682034207343827)
      ·
        refine ⟨5736817511523051311015741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3824545007682034207343827 5736817511523051311015741)
        ·
          refine ⟨2151306566821144241630903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5736817511523051311015741 2151306566821144241630903)
          ·
            refine ⟨3226959850231716362446355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151306566821144241630903 3226959850231716362446355)
            ·
              refine ⟨4840439775347574543669533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3226959850231716362446355 4840439775347574543669533)
              ·
                refine ⟨1815164915755340453876075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4840439775347574543669533 1815164915755340453876075)
                ·
                  refine ⟨2722747373633010680814113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1815164915755340453876075 2722747373633010680814113)
                  ·
                    refine ⟨2042060530224758010610585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2722747373633010680814113 2042060530224758010610585)
                    ·
                      refine ⟨1531545397668568507957939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2042060530224758010610585 1531545397668568507957939)
                      ·
                        rfl

theorem cell23_2982674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_2982674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982674 prefixEnd_2982674 := by exact prefixLift 2982674
  have htrace : WordTrace (prefixWord ++ tailWord_2982674) baseStart_2982674 baseEnd_2982674 := by
    simpa [prefixWord, tailWord_2982674, baseEnd_2982674] using wordTrace_append hprefix tailTrace_2982674
  have hstable : (prefixWord ++ tailWord_2982674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982674).length < 2 ^ (prefixWord ++ tailWord_2982674).sum := by decide
  have hdescent : baseEnd_2982674 < baseStart_2982674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982682 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5]
def baseStart_2982682 : Nat := 118140960795 + 2982682 * 2 ^ 59
def prefixEnd_2982682 : Nat := 4983230072969 + 3 ^ 40 * 2982682 * 2
def baseEnd_2982682 : Nat := 1531549505513804476657901

theorem tailTrace_2982682 : CollatzResearch.WordTrace tailWord_2982682 prefixEnd_2982682 1531549505513804476657901 := by
  unfold tailWord_2982682
  simp only [CollatzResearch.WordTrace]
  refine ⟨27196837445064997593795575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72524899853506660250121533 27196837445064997593795575)
  ·
    refine ⟨40795256167597496390693363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27196837445064997593795575 40795256167597496390693363)
    ·
      refine ⟨61192884251396244586040045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40795256167597496390693363 61192884251396244586040045)
      ·
        refine ⟨22947331594273591719765017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61192884251396244586040045 22947331594273591719765017)
        ·
          refine ⟨17210498695705193789823763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22947331594273591719765017 17210498695705193789823763)
          ·
            refine ⟨25815748043557790684735645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17210498695705193789823763 25815748043557790684735645)
            ·
              refine ⟨9680905516334171506775867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25815748043557790684735645 9680905516334171506775867)
              ·
                refine ⟨14521358274501257260163801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9680905516334171506775867 14521358274501257260163801)
                ·
                  refine ⟨10891018705875942945122851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14521358274501257260163801 10891018705875942945122851)
                  ·
                    refine ⟨16336528058813914417684277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10891018705875942945122851 16336528058813914417684277)
                    ·
                      refine ⟨1531549505513804476657901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16336528058813914417684277 1531549505513804476657901)
                      ·
                        rfl

theorem cell23_2982682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_2982682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982682 prefixEnd_2982682 := by exact prefixLift 2982682
  have htrace : WordTrace (prefixWord ++ tailWord_2982682) baseStart_2982682 baseEnd_2982682 := by
    simpa [prefixWord, tailWord_2982682, baseEnd_2982682] using wordTrace_append hprefix tailTrace_2982682
  have hstable : (prefixWord ++ tailWord_2982682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982682).length < 2 ^ (prefixWord ++ tailWord_2982682).sum := by decide
  have hdescent : baseEnd_2982682 < baseStart_2982682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982696 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_2982696 : Nat := 118140960795 + 2982696 * 2 ^ 59
def prefixEnd_2982696 : Nat := 4983230072969 + 3 ^ 40 * 2982696 * 2
def baseEnd_2982696 : Nat := 1531556694242967421882837

theorem tailTrace_2982696 : CollatzResearch.WordTrace tailWord_2982696 prefixEnd_2982696 1531556694242967421882837 := by
  unfold tailWord_2982696
  simp only [CollatzResearch.WordTrace]
  refine ⟨54393930201104635383095971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72525240268139513844127961 54393930201104635383095971)
  ·
    refine ⟨81590895301656953074643957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54393930201104635383095971 81590895301656953074643957)
    ·
      refine ⟨7649146434530339350747871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81590895301656953074643957 7649146434530339350747871)
      ·
        refine ⟨11473719651795509026121807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7649146434530339350747871 11473719651795509026121807)
        ·
          refine ⟨17210579477693263539182711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11473719651795509026121807 17210579477693263539182711)
          ·
            refine ⟨25815869216539895308774067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17210579477693263539182711 25815869216539895308774067)
            ·
              refine ⟨38723803824809842963161101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25815869216539895308774067 38723803824809842963161101)
              ·
                refine ⟨14521426434303691111185413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38723803824809842963161101 14521426434303691111185413)
                ·
                  refine ⟨2722767456431942083347265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14521426434303691111185413 2722767456431942083347265)
                  ·
                    refine ⟨2042075592323956562510449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2722767456431942083347265 2042075592323956562510449)
                    ·
                      refine ⟨1531556694242967421882837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2042075592323956562510449 1531556694242967421882837)
                      ·
                        rfl

theorem cell23_2982696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_2982696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982696 prefixEnd_2982696 := by exact prefixLift 2982696
  have htrace : WordTrace (prefixWord ++ tailWord_2982696) baseStart_2982696 baseEnd_2982696 := by
    simpa [prefixWord, tailWord_2982696, baseEnd_2982696] using wordTrace_append hprefix tailTrace_2982696
  have hstable : (prefixWord ++ tailWord_2982696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982696).length < 2 ^ (prefixWord ++ tailWord_2982696).sum := by decide
  have hdescent : baseEnd_2982696 < baseStart_2982696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982712 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 1, 5, 3]
def baseStart_2982712 : Nat := 118140960795 + 2982712 * 2 ^ 59
def prefixEnd_2982712 : Nat := 4983230072969 + 3 ^ 40 * 2982712 * 2
def baseEnd_2982712 : Nat := 1531564909933439359282763

theorem tailTrace_2982712 : CollatzResearch.WordTrace tailWord_2982712 prefixEnd_2982712 1531564909933439359282763 := by
  unfold tailWord_2982712
  simp only [CollatzResearch.WordTrace]
  refine ⟨54394221985075652749387195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72525629313434203665849593 54394221985075652749387195)
  ·
    refine ⟨81591332977613479124080793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54394221985075652749387195 81591332977613479124080793)
    ·
      refine ⟨61193499733210109343060595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81591332977613479124080793 61193499733210109343060595)
      ·
        refine ⟨91790249599815164014590893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61193499733210109343060595 91790249599815164014590893)
        ·
          refine ⟨34421343599930686505471585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91790249599815164014590893 34421343599930686505471585)
          ·
            refine ⟨25816007699948014879103689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34421343599930686505471585 25816007699948014879103689)
            ·
              refine ⟨19362005774961011159327767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25816007699948014879103689 19362005774961011159327767)
              ·
                refine ⟨29043008662441516738991651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19362005774961011159327767 29043008662441516738991651)
                ·
                  refine ⟨43564512993662275108487477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29043008662441516738991651 43564512993662275108487477)
                  ·
                    refine ⟨4084173093155838291420701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43564512993662275108487477 4084173093155838291420701)
                    ·
                      refine ⟨1531564909933439359282763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4084173093155838291420701 1531564909933439359282763)
                      ·
                        rfl

theorem cell23_2982712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_2982712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982712 prefixEnd_2982712 := by exact prefixLift 2982712
  have htrace : WordTrace (prefixWord ++ tailWord_2982712) baseStart_2982712 baseEnd_2982712 := by
    simpa [prefixWord, tailWord_2982712, baseEnd_2982712] using wordTrace_append hprefix tailTrace_2982712
  have hstable : (prefixWord ++ tailWord_2982712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982712).length < 2 ^ (prefixWord ++ tailWord_2982712).sum := by decide
  have hdescent : baseEnd_2982712 < baseStart_2982712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982769 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 1, 6, 2]
def baseStart_2982769 : Nat := 118140960795 + 2982769 * 2 ^ 59
def prefixEnd_2982769 : Nat := 4983230072969 + 3 ^ 40 * 2982769 * 2
def baseEnd_2982769 : Nat := 1531594178330745636270001

theorem tailTrace_2982769 : CollatzResearch.WordTrace tailWord_2982769 prefixEnd_2982769 1531594178330745636270001 := by
  unfold tailWord_2982769
  simp only [CollatzResearch.WordTrace]
  refine ⟨108790522930944804233599361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72527015287296536155732907 108790522930944804233599361)
  ·
    refine ⟨81592892198208603175199521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108790522930944804233599361 81592892198208603175199521)
    ·
      refine ⟨61194669148656452381399641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81592892198208603175199521 61194669148656452381399641)
      ·
        refine ⟨45896001861492339286049731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61194669148656452381399641 45896001861492339286049731)
        ·
          refine ⟨68844002792238508929074597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45896001861492339286049731 68844002792238508929074597)
          ·
            refine ⟨12908250523544720424201487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68844002792238508929074597 12908250523544720424201487)
            ·
              refine ⟨19362375785317080636302231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12908250523544720424201487 19362375785317080636302231)
              ·
                refine ⟨29043563677975620954453347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19362375785317080636302231 29043563677975620954453347)
                ·
                  refine ⟨43565345516963431431680021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29043563677975620954453347 43565345516963431431680021)
                  ·
                    refine ⟨2042125571107660848360001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43565345516963431431680021 2042125571107660848360001)
                    ·
                      refine ⟨1531594178330745636270001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2042125571107660848360001 1531594178330745636270001)
                      ·
                        rfl

theorem cell23_2982769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_2982769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982769 prefixEnd_2982769 := by exact prefixLift 2982769
  have htrace : WordTrace (prefixWord ++ tailWord_2982769) baseStart_2982769 baseEnd_2982769 := by
    simpa [prefixWord, tailWord_2982769, baseEnd_2982769] using wordTrace_append hprefix tailTrace_2982769
  have hstable : (prefixWord ++ tailWord_2982769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982769).length < 2 ^ (prefixWord ++ tailWord_2982769).sum := by decide
  have hdescent : baseEnd_2982769 < baseStart_2982769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982789 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 1, 4, 3]
def baseStart_2982789 : Nat := 118140960795 + 2982789 * 2 ^ 59
def prefixEnd_2982789 : Nat := 4983230072969 + 3 ^ 40 * 2982789 * 2
def baseEnd_2982789 : Nat := 1531604447943835558019909

theorem tailTrace_2982789 : CollatzResearch.WordTrace tailWord_2982789 prefixEnd_2982789 1531604447943835558019909 := by
  unfold tailWord_2982789
  simp only [CollatzResearch.WordTrace]
  refine ⟨108791252390872347649327421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72527501593914898432884947 108791252390872347649327421)
  ·
    refine ⟨40796719646577130368497783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108791252390872347649327421 40796719646577130368497783)
    ·
      refine ⟨61195079469865695552746675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40796719646577130368497783 61195079469865695552746675)
      ·
        refine ⟨91792619204798543329120013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61195079469865695552746675 91792619204798543329120013)
        ·
          refine ⟨34422232201799453748420005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91792619204798543329120013 34422232201799453748420005)
          ·
            refine ⟨6454168537837397577828751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34422232201799453748420005 6454168537837397577828751)
            ·
              refine ⟨9681252806756096366743127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6454168537837397577828751 9681252806756096366743127)
              ·
                refine ⟨14521879210134144550114691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9681252806756096366743127 14521879210134144550114691)
                ·
                  refine ⟨21782818815201216825172037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14521879210134144550114691 21782818815201216825172037)
                  ·
                    refine ⟨4084278527850228154719757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21782818815201216825172037 4084278527850228154719757)
                    ·
                      refine ⟨1531604447943835558019909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4084278527850228154719757 1531604447943835558019909)
                      ·
                        rfl

theorem cell23_2982789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_2982789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982789 prefixEnd_2982789 := by exact prefixLift 2982789
  have htrace : WordTrace (prefixWord ++ tailWord_2982789) baseStart_2982789 baseEnd_2982789 := by
    simpa [prefixWord, tailWord_2982789, baseEnd_2982789] using wordTrace_append hprefix tailTrace_2982789
  have hstable : (prefixWord ++ tailWord_2982789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982789).length < 2 ^ (prefixWord ++ tailWord_2982789).sum := by decide
  have hdescent : baseEnd_2982789 < baseStart_2982789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982796 : List Nat := [2, 2, 1, 2, 1, 2, 3, 5, 1, 4]
def baseStart_2982796 : Nat := 118140960795 + 2982796 * 2 ^ 59
def prefixEnd_2982796 : Nat := 4983230072969 + 3 ^ 40 * 2982796 * 2
def baseEnd_2982796 : Nat := 510536014102805676877459

theorem tailTrace_2982796 : CollatzResearch.WordTrace tailWord_2982796 prefixEnd_2982796 510536014102805676877459 := by
  unfold tailWord_2982796
  simp only [CollatzResearch.WordTrace]
  refine ⟨54395753850923493922416121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72527671801231325229888161 54395753850923493922416121)
  ·
    refine ⟨40796815388192620441812091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54395753850923493922416121 40796815388192620441812091)
    ·
      refine ⟨61195223082288930662718137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40796815388192620441812091 61195223082288930662718137)
      ·
        refine ⟨45896417311716697997038603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61195223082288930662718137 45896417311716697997038603)
        ·
          refine ⟨68844625967575046995557905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45896417311716697997038603 68844625967575046995557905)
          ·
            refine ⟨51633469475681285246668429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68844625967575046995557905 51633469475681285246668429)
            ·
              refine ⟨19362551053380481967500661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51633469475681285246668429 19362551053380481967500661)
              ·
                refine ⟨1815239161254420184453187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19362551053380481967500661 1815239161254420184453187)
                ·
                  refine ⟨2722858741881630276679781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1815239161254420184453187 2722858741881630276679781)
                  ·
                    refine ⟨510536014102805676877459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2722858741881630276679781 510536014102805676877459)
                    ·
                      rfl

theorem cell23_2982796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 1, 4].length) (baseStart_2982796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982796 prefixEnd_2982796 := by exact prefixLift 2982796
  have htrace : WordTrace (prefixWord ++ tailWord_2982796) baseStart_2982796 baseEnd_2982796 := by
    simpa [prefixWord, tailWord_2982796, baseEnd_2982796] using wordTrace_append hprefix tailTrace_2982796
  have hstable : (prefixWord ++ tailWord_2982796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982796).length < 2 ^ (prefixWord ++ tailWord_2982796).sum := by decide
  have hdescent : baseEnd_2982796 < baseStart_2982796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982839 : List Nat := [1, 1, 3, 1, 3, 1, 3, 4, 1, 5]
def baseStart_2982839 : Nat := 118140960795 + 2982839 * 2 ^ 59
def prefixEnd_2982839 : Nat := 4983230072969 + 3 ^ 40 * 2982839 * 2
def baseEnd_2982839 : Nat := 510543373992186787464893

theorem tailTrace_2982839 : CollatzResearch.WordTrace tailWord_2982839 prefixEnd_2982839 510543373992186787464893 := by
  unfold tailWord_2982839
  simp only [CollatzResearch.WordTrace]
  refine ⟨108793076040691206188647571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72528717360460804125765047 108793076040691206188647571)
  ·
    refine ⟨163189614061036809282971357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108793076040691206188647571 163189614061036809282971357)
    ·
      refine ⟨61196105272888803481114259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163189614061036809282971357 61196105272888803481114259)
      ·
        refine ⟨91794157909333205221671389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61196105272888803481114259 91794157909333205221671389)
        ·
          refine ⟨34422809215999951958126771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91794157909333205221671389 34422809215999951958126771)
          ·
            refine ⟨51634213823999927937190157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34422809215999951958126771 51634213823999927937190157)
            ·
              refine ⟨19362830183999972976446309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51634213823999927937190157 19362830183999972976446309)
              ·
                refine ⟨3630530659499994933083683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19362830183999972976446309 3630530659499994933083683)
                ·
                  refine ⟨5445795989249992399625525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3630530659499994933083683 5445795989249992399625525)
                  ·
                    refine ⟨510543373992186787464893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5445795989249992399625525 510543373992186787464893)
                    ·
                      rfl

theorem cell23_2982839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_2982839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982839 prefixEnd_2982839 := by exact prefixLift 2982839
  have htrace : WordTrace (prefixWord ++ tailWord_2982839) baseStart_2982839 baseEnd_2982839 := by
    simpa [prefixWord, tailWord_2982839, baseEnd_2982839] using wordTrace_append hprefix tailTrace_2982839
  have hstable : (prefixWord ++ tailWord_2982839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982839).length < 2 ^ (prefixWord ++ tailWord_2982839).sum := by decide
  have hdescent : baseEnd_2982839 < baseStart_2982839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982846 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2]
def baseStart_2982846 : Nat := 118140960795 + 2982846 * 2 ^ 59
def prefixEnd_2982846 : Nat := 4983230072969 + 3 ^ 40 * 2982846 * 2
def baseEnd_2982846 : Nat := 1531633716341141835007147

theorem tailTrace_2982846 : CollatzResearch.WordTrace tailWord_2982846 prefixEnd_2982846 1531633716341141835007147 := by
  unfold tailWord_2982846
  simp only [CollatzResearch.WordTrace]
  refine ⟨13599166418958230798019049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72528887567777230922768261 13599166418958230798019049)
  ·
    refine ⟨10199374814218673098514287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13599166418958230798019049 10199374814218673098514287)
    ·
      refine ⟨15299062221328009647771431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10199374814218673098514287 15299062221328009647771431)
      ·
        refine ⟨22948593331992014471657147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15299062221328009647771431 22948593331992014471657147)
        ·
          refine ⟨34422889997988021707485721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22948593331992014471657147 34422889997988021707485721)
          ·
            refine ⟨25817167498491016280614291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34422889997988021707485721 25817167498491016280614291)
            ·
              refine ⟨38725751247736524420921437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25817167498491016280614291 38725751247736524420921437)
              ·
                refine ⟨14522156717901196657845539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38725751247736524420921437 14522156717901196657845539)
                ·
                  refine ⟨21783235076851794986768309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14522156717901196657845539 21783235076851794986768309)
                  ·
                    refine ⟨2042178288454855780009529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21783235076851794986768309 2042178288454855780009529)
                    ·
                      refine ⟨1531633716341141835007147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2042178288454855780009529 1531633716341141835007147)
                      ·
                        rfl

theorem cell23_2982846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_2982846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982846 prefixEnd_2982846 := by exact prefixLift 2982846
  have htrace : WordTrace (prefixWord ++ tailWord_2982846) baseStart_2982846 baseEnd_2982846 := by
    simpa [prefixWord, tailWord_2982846, baseEnd_2982846] using wordTrace_append hprefix tailTrace_2982846
  have hstable : (prefixWord ++ tailWord_2982846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982846).length < 2 ^ (prefixWord ++ tailWord_2982846).sum := by decide
  have hdescent : baseEnd_2982846 < baseStart_2982846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982870 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_2982870 : Nat := 118140960795 + 2982870 * 2 ^ 59
def prefixEnd_2982870 : Nat := 4983230072969 + 3 ^ 40 * 2982870 * 2
def baseEnd_2982870 : Nat := 1531646039876849741107037

theorem tailTrace_2982870 : CollatzResearch.WordTrace tailWord_2982870 prefixEnd_2982870 1531646039876849741107037 := by
  unfold tailWord_2982870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6799637918973681155189129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72529471135719265655350709 6799637918973681155189129)
  ·
    refine ⟨5099728439230260866391847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6799637918973681155189129 5099728439230260866391847)
    ·
      refine ⟨7649592658845391299587771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5099728439230260866391847 7649592658845391299587771)
      ·
        refine ⟨11474388988268086949381657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7649592658845391299587771 11474388988268086949381657)
        ·
          refine ⟨8605791741201065212036243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11474388988268086949381657 8605791741201065212036243)
          ·
            refine ⟨12908687611801597818054365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8605791741201065212036243 12908687611801597818054365)
            ·
              refine ⟨4840757854425599181770387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12908687611801597818054365 4840757854425599181770387)
              ·
                refine ⟨7261136781638398772655581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4840757854425599181770387 7261136781638398772655581)
                ·
                  refine ⟨2722926293114399539745843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7261136781638398772655581 2722926293114399539745843)
                  ·
                    refine ⟨4084389439671599309618765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2722926293114399539745843 4084389439671599309618765)
                    ·
                      refine ⟨1531646039876849741107037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4084389439671599309618765 1531646039876849741107037)
                      ·
                        rfl

theorem cell23_2982870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_2982870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982870 prefixEnd_2982870 := by exact prefixLift 2982870
  have htrace : WordTrace (prefixWord ++ tailWord_2982870) baseStart_2982870 baseEnd_2982870 := by
    simpa [prefixWord, tailWord_2982870, baseEnd_2982870] using wordTrace_append hprefix tailTrace_2982870
  have hstable : (prefixWord ++ tailWord_2982870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982870).length < 2 ^ (prefixWord ++ tailWord_2982870).sum := by decide
  have hdescent : baseEnd_2982870 < baseStart_2982870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982943 : List Nat := [1, 1, 2, 4, 1, 3, 2, 3, 2, 1, 3]
def baseStart_2982943 : Nat := 118140960795 + 2982943 * 2 ^ 59
def prefixEnd_2982943 : Nat := 4983230072969 + 3 ^ 40 * 2982943 * 2
def baseEnd_2982943 : Nat := 1531683523964627955494201

theorem tailTrace_2982943 : CollatzResearch.WordTrace tailWord_2982943 prefixEnd_2982943 1531683523964627955494201 := by
  unfold tailWord_2982943
  simp only [CollatzResearch.WordTrace]
  refine ⟨108796869232314431950433483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72531246154876287966955655 108796869232314431950433483)
  ·
    refine ⟨163195303848471647925650225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108796869232314431950433483 163195303848471647925650225)
    ·
      refine ⟨122396477886353735944237669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163195303848471647925650225 122396477886353735944237669)
      ·
        refine ⟨22949339603691325489544563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122396477886353735944237669 22949339603691325489544563)
        ·
          refine ⟨34424009405536988234316845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22949339603691325489544563 34424009405536988234316845)
          ·
            refine ⟨12909003527076370587868817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34424009405536988234316845 12909003527076370587868817)
            ·
              refine ⟨9681752645307277940901613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12909003527076370587868817 9681752645307277940901613)
              ·
                refine ⟨3630657241990229227838105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9681752645307277940901613 3630657241990229227838105)
                ·
                  refine ⟨2722992931492671920878579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3630657241990229227838105 2722992931492671920878579)
                  ·
                    refine ⟨4084489397239007881317869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2722992931492671920878579 4084489397239007881317869)
                    ·
                      refine ⟨1531683523964627955494201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4084489397239007881317869 1531683523964627955494201)
                      ·
                        rfl

theorem cell23_2982943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_2982943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982943 prefixEnd_2982943 := by exact prefixLift 2982943
  have htrace : WordTrace (prefixWord ++ tailWord_2982943) baseStart_2982943 baseEnd_2982943 := by
    simpa [prefixWord, tailWord_2982943, baseEnd_2982943] using wordTrace_append hprefix tailTrace_2982943
  have hstable : (prefixWord ++ tailWord_2982943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982943).length < 2 ^ (prefixWord ++ tailWord_2982943).sum := by decide
  have hdescent : baseEnd_2982943 < baseStart_2982943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982949 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 2, 3, 4]
def baseStart_2982949 : Nat := 118140960795 + 2982949 * 2 ^ 59
def prefixEnd_2982949 : Nat := 4983230072969 + 3 ^ 40 * 2982949 * 2
def baseEnd_2982949 : Nat := 1531686604848554932019173

theorem tailTrace_2982949 : CollatzResearch.WordTrace tailWord_2982949 prefixEnd_2982949 1531686604848554932019173 := by
  unfold tailWord_2982949
  simp only [CollatzResearch.WordTrace]
  refine ⟨108797088070292694975151901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72531392046861796650101267 108797088070292694975151901)
  ·
    refine ⟨40798908026359760615681963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108797088070292694975151901 40798908026359760615681963)
    ·
      refine ⟨61198362039539640923522945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40798908026359760615681963 61198362039539640923522945)
      ·
        refine ⟨45898771529654730692642209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61198362039539640923522945 45898771529654730692642209)
        ·
          refine ⟨34424078647241048019481657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45898771529654730692642209 34424078647241048019481657)
          ·
            refine ⟨25818058985430786014611243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34424078647241048019481657 25818058985430786014611243)
            ·
              refine ⟨38727088478146179021916865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25818058985430786014611243 38727088478146179021916865)
              ·
                refine ⟨29045316358609634266437649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38727088478146179021916865 29045316358609634266437649)
                ·
                  refine ⟨21783987268957225699828237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29045316358609634266437649 21783987268957225699828237)
                  ·
                    refine ⟨8168995225858959637435589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21783987268957225699828237 8168995225858959637435589)
                    ·
                      refine ⟨1531686604848554932019173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8168995225858959637435589 1531686604848554932019173)
                      ·
                        rfl

theorem cell23_2982949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_2982949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982949 prefixEnd_2982949 := by exact prefixLift 2982949
  have htrace : WordTrace (prefixWord ++ tailWord_2982949) baseStart_2982949 baseEnd_2982949 := by
    simpa [prefixWord, tailWord_2982949, baseEnd_2982949] using wordTrace_append hprefix tailTrace_2982949
  have hstable : (prefixWord ++ tailWord_2982949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982949).length < 2 ^ (prefixWord ++ tailWord_2982949).sum := by decide
  have hdescent : baseEnd_2982949 < baseStart_2982949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982970 : List Nat := [3, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2]
def baseStart_2982970 : Nat := 118140960795 + 2982970 * 2 ^ 59
def prefixEnd_2982970 : Nat := 4983230072969 + 3 ^ 40 * 2982970 * 2
def baseEnd_2982970 : Nat := 1531697387942299349856577

theorem tailTrace_2982970 : CollatzResearch.WordTrace tailWord_2982970 prefixEnd_2982970 1531697387942299349856577 := by
  unfold tailWord_2982970
  simp only [CollatzResearch.WordTrace]
  refine ⟨27199463500804153890416591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72531902668811077041110909 27199463500804153890416591)
  ·
    refine ⟨40799195251206230835624887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27199463500804153890416591 40799195251206230835624887)
    ·
      refine ⟨61198792876809346253437331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40799195251206230835624887 61198792876809346253437331)
      ·
        refine ⟨91798189315214019380155997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61198792876809346253437331 91798189315214019380155997)
        ·
          refine ⟨34424320993205257267558499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91798189315214019380155997 34424320993205257267558499)
          ·
            refine ⟨51636481489807885901337749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34424320993205257267558499 51636481489807885901337749)
            ·
              refine ⟨2420460069834744651625207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51636481489807885901337749 2420460069834744651625207)
              ·
                refine ⟨3630690104752116977437811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2420460069834744651625207 3630690104752116977437811)
                ·
                  refine ⟨5446035157128175466156717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3630690104752116977437811 5446035157128175466156717)
                  ·
                    refine ⟨2042263183923065799808769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5446035157128175466156717 2042263183923065799808769)
                    ·
                      refine ⟨1531697387942299349856577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2042263183923065799808769 1531697387942299349856577)
                      ·
                        rfl

theorem cell23_2982970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2].length) (baseStart_2982970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982970 prefixEnd_2982970 := by exact prefixLift 2982970
  have htrace : WordTrace (prefixWord ++ tailWord_2982970) baseStart_2982970 baseEnd_2982970 := by
    simpa [prefixWord, tailWord_2982970, baseEnd_2982970] using wordTrace_append hprefix tailTrace_2982970
  have hstable : (prefixWord ++ tailWord_2982970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982970).length < 2 ^ (prefixWord ++ tailWord_2982970).sum := by decide
  have hdescent : baseEnd_2982970 < baseStart_2982970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982977 : List Nat := [1, 2, 5, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_2982977 : Nat := 118140960795 + 2982977 * 2 ^ 59
def prefixEnd_2982977 : Nat := 4983230072969 + 3 ^ 40 * 2982977 * 2
def baseEnd_2982977 : Nat := 1531700982306880822469045

theorem tailTrace_2982977 : CollatzResearch.WordTrace tailWord_2982977 prefixEnd_2982977 1531700982306880822469045 := by
  unfold tailWord_2982977
  simp only [CollatzResearch.WordTrace]
  refine ⟨108798109314191255757171185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72532072876127503838114123 108798109314191255757171185)
  ·
    refine ⟨81598581985643441817878389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108798109314191255757171185 81598581985643441817878389)
    ·
      refine ⟨7649867061154072670426099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81598581985643441817878389 7649867061154072670426099)
      ·
        refine ⟨11474800591731109005639149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7649867061154072670426099 11474800591731109005639149)
        ·
          refine ⟨4303050221899165877114681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11474800591731109005639149 4303050221899165877114681)
          ·
            refine ⟨3227287666424374407836011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4303050221899165877114681 3227287666424374407836011)
            ·
              refine ⟨4840931499636561611754017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3227287666424374407836011 4840931499636561611754017)
              ·
                refine ⟨3630698624727421208815513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4840931499636561611754017 3630698624727421208815513)
                ·
                  refine ⟨2723023968545565906611635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3630698624727421208815513 2723023968545565906611635)
                  ·
                    refine ⟨4084535952818348859917453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2723023968545565906611635 4084535952818348859917453)
                    ·
                      refine ⟨1531700982306880822469045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4084535952818348859917453 1531700982306880822469045)
                      ·
                        rfl

theorem cell23_2982977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_2982977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982977 prefixEnd_2982977 := by exact prefixLift 2982977
  have htrace : WordTrace (prefixWord ++ tailWord_2982977) baseStart_2982977 baseEnd_2982977 := by
    simpa [prefixWord, tailWord_2982977, baseEnd_2982977] using wordTrace_append hprefix tailTrace_2982977
  have hstable : (prefixWord ++ tailWord_2982977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982977).length < 2 ^ (prefixWord ++ tailWord_2982977).sum := by decide
  have hdescent : baseEnd_2982977 < baseStart_2982977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982979 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 4]
def baseStart_2982979 : Nat := 118140960795 + 2982979 * 2 ^ 59
def prefixEnd_2982979 : Nat := 4983230072969 + 3 ^ 40 * 2982979 * 2
def baseEnd_2982979 : Nat := 1531702009268189814644035

theorem tailTrace_2982979 : CollatzResearch.WordTrace tailWord_2982979 prefixEnd_2982979 1531702009268189814644035 := by
  unfold tailWord_2982979
  simp only [CollatzResearch.WordTrace]
  refine ⟨108798182260184010098743991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72532121506789340065829327 108798182260184010098743991)
  ·
    refine ⟨163197273390276015148115987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108798182260184010098743991 163197273390276015148115987)
    ·
      refine ⟨244795910085414022722173981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163197273390276015148115987 244795910085414022722173981)
      ·
        refine ⟨91798466282030258520815243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244795910085414022722173981 91798466282030258520815243)
        ·
          refine ⟨137697699423045387781222865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91798466282030258520815243 137697699423045387781222865)
          ·
            refine ⟨103273274567284040835917149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137697699423045387781222865 103273274567284040835917149)
            ·
              refine ⟨38727477962731515313468931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103273274567284040835917149 38727477962731515313468931)
              ·
                refine ⟨58091216944097272970203397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38727477962731515313468931 58091216944097272970203397)
                ·
                  refine ⟨10892103177018238681913137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58091216944097272970203397 10892103177018238681913137)
                  ·
                    refine ⟨8169077382763679011434853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10892103177018238681913137 8169077382763679011434853)
                    ·
                      refine ⟨1531702009268189814644035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8169077382763679011434853 1531702009268189814644035)
                      ·
                        rfl

theorem cell23_2982979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_2982979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982979 prefixEnd_2982979 := by exact prefixLift 2982979
  have htrace : WordTrace (prefixWord ++ tailWord_2982979) baseStart_2982979 baseEnd_2982979 := by
    simpa [prefixWord, tailWord_2982979, baseEnd_2982979] using wordTrace_append hprefix tailTrace_2982979
  have hstable : (prefixWord ++ tailWord_2982979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982979).length < 2 ^ (prefixWord ++ tailWord_2982979).sum := by decide
  have hdescent : baseEnd_2982979 < baseStart_2982979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2982996 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_2982996 : Nat := 118140960795 + 2982996 * 2 ^ 59
def prefixEnd_2982996 : Nat := 4983230072969 + 3 ^ 40 * 2982996 * 2
def baseEnd_2982996 : Nat := 1531710738439316248131457

theorem tailTrace_2982996 : CollatzResearch.WordTrace tailWord_2982996 prefixEnd_2982996 1531710738439316248131457 := by
  unfold tailWord_2982996
  simp only [CollatzResearch.WordTrace]
  refine ⟨54399401150561211001056421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72532534867414948001408561 54399401150561211001056421)
  ·
    refine ⟨10199887715730227062698079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54399401150561211001056421 10199887715730227062698079)
    ·
      refine ⟨15299831573595340594047119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10199887715730227062698079 15299831573595340594047119)
      ·
        refine ⟨22949747360393010891070679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15299831573595340594047119 22949747360393010891070679)
        ·
          refine ⟨34424621040589516336606019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22949747360393010891070679 34424621040589516336606019)
          ·
            refine ⟨51636931560884274504909029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34424621040589516336606019 51636931560884274504909029)
            ·
              refine ⟨9681924667665801469670443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51636931560884274504909029 9681924667665801469670443)
              ·
                refine ⟨14522887001498702204505665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9681924667665801469670443 14522887001498702204505665)
                ·
                  refine ⟨10892165251124026653379249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14522887001498702204505665 10892165251124026653379249)
                  ·
                    refine ⟨8169123938343019990034437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10892165251124026653379249 8169123938343019990034437)
                    ·
                      refine ⟨1531710738439316248131457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8169123938343019990034437 1531710738439316248131457)
                      ·
                        rfl

theorem cell23_2982996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_2982996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2982996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2982996 prefixEnd_2982996 := by exact prefixLift 2982996
  have htrace : WordTrace (prefixWord ++ tailWord_2982996) baseStart_2982996 baseEnd_2982996 := by
    simpa [prefixWord, tailWord_2982996, baseEnd_2982996] using wordTrace_append hprefix tailTrace_2982996
  have hstable : (prefixWord ++ tailWord_2982996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2982996).length < 2 ^ (prefixWord ++ tailWord_2982996).sum := by decide
  have hdescent : baseEnd_2982996 < baseStart_2982996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2982996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983019 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 8, 5]
def baseStart_2983019 : Nat := 118140960795 + 2983019 * 2 ^ 59
def prefixEnd_2983019 : Nat := 4983230072969 + 3 ^ 40 * 2983019 * 2
def baseEnd_2983019 : Nat := 510574182831456552714617

theorem tailTrace_2983019 : CollatzResearch.WordTrace tailWord_2983019 prefixEnd_2983019 510574182831456552714617 := by
  unfold tailWord_2983019
  simp only [CollatzResearch.WordTrace]
  refine ⟨108799641180039096930200111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72533094120026064620133407 108799641180039096930200111)
  ·
    refine ⟨163199461770058645395300167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108799641180039096930200111 163199461770058645395300167)
    ·
      refine ⟨244799192655087968092950251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163199461770058645395300167 244799192655087968092950251)
      ·
        refine ⟨367198788982631952139425377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244799192655087968092950251 367198788982631952139425377)
        ·
          refine ⟨275399091736973964104569033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367198788982631952139425377 275399091736973964104569033)
          ·
            refine ⟨206549318802730473078426775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275399091736973964104569033 206549318802730473078426775)
            ·
              refine ⟨309823978204095709617640163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206549318802730473078426775 309823978204095709617640163)
              ·
                refine ⟨464735967306143564426460245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309823978204095709617640163 464735967306143564426460245)
                ·
                  refine ⟨5446124616868869895622581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 464735967306143564426460245 5446124616868869895622581)
                  ·
                    refine ⟨510574182831456552714617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5446124616868869895622581 510574182831456552714617)
                    ·
                      rfl

theorem cell23_2983019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 5].length) (baseStart_2983019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983019 prefixEnd_2983019 := by exact prefixLift 2983019
  have htrace : WordTrace (prefixWord ++ tailWord_2983019) baseStart_2983019 baseEnd_2983019 := by
    simpa [prefixWord, tailWord_2983019, baseEnd_2983019] using wordTrace_append hprefix tailTrace_2983019
  have hstable : (prefixWord ++ tailWord_2983019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983019).length < 2 ^ (prefixWord ++ tailWord_2983019).sum := by decide
  have hdescent : baseEnd_2983019 < baseStart_2983019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983036 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 2, 5]
def baseStart_2983036 : Nat := 118140960795 + 2983036 * 2 ^ 59
def prefixEnd_2983036 : Nat := 4983230072969 + 3 ^ 40 * 2983036 * 2
def baseEnd_2983036 : Nat := 510577092555165363877091

theorem tailTrace_2983036 : CollatzResearch.WordTrace tailWord_2983036 prefixEnd_2983036 510577092555165363877091 := by
  unfold tailWord_2983036
  simp only [CollatzResearch.WordTrace]
  refine ⟨54400130610488754416784481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72533507480651672555712641 54400130610488754416784481)
  ·
    refine ⟨40800097957866565812588361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54400130610488754416784481 40800097957866565812588361)
    ·
      refine ⟨30600073468399924359441271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40800097957866565812588361 30600073468399924359441271)
      ·
        refine ⟨45900110202599886539161907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30600073468399924359441271 45900110202599886539161907)
        ·
          refine ⟨68850165303899829808742861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45900110202599886539161907 68850165303899829808742861)
          ·
            refine ⟨25818811988962436178278573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68850165303899829808742861 25818811988962436178278573)
            ·
              refine ⟨9682054495860913566854465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25818811988962436178278573 9682054495860913566854465)
              ·
                refine ⟨7261540871895685175140849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9682054495860913566854465 7261540871895685175140849)
                ·
                  refine ⟨5446155653921763881355637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7261540871895685175140849 5446155653921763881355637)
                  ·
                    refine ⟨510577092555165363877091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5446155653921763881355637 510577092555165363877091)
                    ·
                      rfl

theorem cell23_2983036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_2983036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983036 prefixEnd_2983036 := by exact prefixLift 2983036
  have htrace : WordTrace (prefixWord ++ tailWord_2983036) baseStart_2983036 baseEnd_2983036 := by
    simpa [prefixWord, tailWord_2983036, baseEnd_2983036] using wordTrace_append hprefix tailTrace_2983036
  have hstable : (prefixWord ++ tailWord_2983036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983036).length < 2 ^ (prefixWord ++ tailWord_2983036).sum := by decide
  have hdescent : baseEnd_2983036 < baseStart_2983036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983039 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 4]
def baseStart_2983039 : Nat := 118140960795 + 2983039 * 2 ^ 59
def prefixEnd_2983039 : Nat := 4983230072969 + 3 ^ 40 * 2983039 * 2
def baseEnd_2983039 : Nat := 1531732818107459579893759

theorem tailTrace_2983039 : CollatzResearch.WordTrace tailWord_2983039 prefixEnd_2983039 1531732818107459579893759 := by
  unfold tailWord_2983039
  simp only [CollatzResearch.WordTrace]
  refine ⟨108800370639966640345928171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72533580426644426897285447 108800370639966640345928171)
  ·
    refine ⟨163200555959949960518892257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108800370639966640345928171 163200555959949960518892257)
    ·
      refine ⟨122400416969962470389169193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163200555959949960518892257 122400416969962470389169193)
      ·
        refine ⟨91800312727471852791876895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122400416969962470389169193 91800312727471852791876895)
        ·
          refine ⟨137700469091207779187815343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91800312727471852791876895 137700469091207779187815343)
          ·
            refine ⟨206550703636811668781723015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137700469091207779187815343 206550703636811668781723015)
            ·
              refine ⟨309826055455217503172584523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206550703636811668781723015 309826055455217503172584523)
              ·
                refine ⟨464739083182826254758876785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309826055455217503172584523 464739083182826254758876785)
                ·
                  refine ⟨348554312387119691069157589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464739083182826254758876785 348554312387119691069157589)
                  ·
                    refine ⟨8169241696573117759433381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 348554312387119691069157589 8169241696573117759433381)
                    ·
                      refine ⟨1531732818107459579893759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8169241696573117759433381 1531732818107459579893759)
                      ·
                        rfl

theorem cell23_2983039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_2983039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983039 prefixEnd_2983039 := by exact prefixLift 2983039
  have htrace : WordTrace (prefixWord ++ tailWord_2983039) baseStart_2983039 baseEnd_2983039 := by
    simpa [prefixWord, tailWord_2983039, baseEnd_2983039] using wordTrace_append hprefix tailTrace_2983039
  have hstable : (prefixWord ++ tailWord_2983039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983039).length < 2 ^ (prefixWord ++ tailWord_2983039).sum := by decide
  have hdescent : baseEnd_2983039 < baseStart_2983039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983070 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_2983070 : Nat := 118140960795 + 2983070 * 2 ^ 59
def prefixEnd_2983070 : Nat := 4983230072969 + 3 ^ 40 * 2983070 * 2
def baseEnd_2983070 : Nat := 510582912002582986202039

theorem tailTrace_2983070 : CollatzResearch.WordTrace tailWord_2983070 prefixEnd_2983070 510582912002582986202039 := by
  unfold tailWord_2983070
  simp only [CollatzResearch.WordTrace]
  refine ⟨13600187662856791580038333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72534334201902888426871109 13600187662856791580038333)
  ·
    refine ⟨5100070373571296842514375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13600187662856791580038333 5100070373571296842514375)
    ·
      refine ⟨7650105560356945263771563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5100070373571296842514375 7650105560356945263771563)
      ·
        refine ⟨11475158340535417895657345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7650105560356945263771563 11475158340535417895657345)
        ·
          refine ⟨8606368755401563421743009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11475158340535417895657345 8606368755401563421743009)
          ·
            refine ⟨6454776566551172566307257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8606368755401563421743009 6454776566551172566307257)
            ·
              refine ⟨4841082424913379424730443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6454776566551172566307257 4841082424913379424730443)
              ·
                refine ⟨7261623637370069137095665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4841082424913379424730443 7261623637370069137095665)
                ·
                  refine ⟨5446217728027551852821749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7261623637370069137095665 5446217728027551852821749)
                  ·
                    refine ⟨510582912002582986202039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5446217728027551852821749 510582912002582986202039)
                    ·
                      rfl

theorem cell23_2983070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_2983070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983070 prefixEnd_2983070 := by exact prefixLift 2983070
  have htrace : WordTrace (prefixWord ++ tailWord_2983070) baseStart_2983070 baseEnd_2983070 := by
    simpa [prefixWord, tailWord_2983070, baseEnd_2983070] using wordTrace_append hprefix tailTrace_2983070
  have hstable : (prefixWord ++ tailWord_2983070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983070).length < 2 ^ (prefixWord ++ tailWord_2983070).sum := by decide
  have hdescent : baseEnd_2983070 < baseStart_2983070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983073 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 2, 1, 4]
def baseStart_2983073 : Nat := 118140960795 + 2983073 * 2 ^ 59
def prefixEnd_2983073 : Nat := 4983230072969 + 3 ^ 40 * 2983073 * 2
def baseEnd_2983073 : Nat := 1531750276449712446868603

theorem tailTrace_2983073 : CollatzResearch.WordTrace tailWord_2983073 prefixEnd_2983073 1531750276449712446868603 := by
  unfold tailWord_2983073
  simp only [CollatzResearch.WordTrace]
  refine ⟨108801610721843464152665873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72534407147895642768443915 108801610721843464152665873)
  ·
    refine ⟨81601208041382598114499405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108801610721843464152665873 81601208041382598114499405)
    ·
      refine ⟨30600453015518474292937277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81601208041382598114499405 30600453015518474292937277)
      ·
        refine ⟨11475169880819427859851479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30600453015518474292937277 11475169880819427859851479)
        ·
          refine ⟨17212754821229141789777219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11475169880819427859851479 17212754821229141789777219)
          ·
            refine ⟨25819132231843712684665829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17212754821229141789777219 25819132231843712684665829)
            ·
              refine ⟨4841087293470696128374843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25819132231843712684665829 4841087293470696128374843)
              ·
                refine ⟨7261630940206044192562265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4841087293470696128374843 7261630940206044192562265)
                ·
                  refine ⟨5446223205154533144421699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7261630940206044192562265 5446223205154533144421699)
                  ·
                    refine ⟨8169334807731799716632549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5446223205154533144421699 8169334807731799716632549)
                    ·
                      refine ⟨1531750276449712446868603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8169334807731799716632549 1531750276449712446868603)
                      ·
                        rfl

theorem cell23_2983073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_2983073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983073 prefixEnd_2983073 := by exact prefixLift 2983073
  have htrace : WordTrace (prefixWord ++ tailWord_2983073) baseStart_2983073 baseEnd_2983073 := by
    simpa [prefixWord, tailWord_2983073, baseEnd_2983073] using wordTrace_append hprefix tailTrace_2983073
  have hstable : (prefixWord ++ tailWord_2983073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983073).length < 2 ^ (prefixWord ++ tailWord_2983073).sum := by decide
  have hdescent : baseEnd_2983073 < baseStart_2983073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983123 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 3, 1, 3]
def baseStart_2983123 : Nat := 118140960795 + 2983123 * 2 ^ 59
def prefixEnd_2983123 : Nat := 4983230072969 + 3 ^ 40 * 2983123 * 2
def baseEnd_2983123 : Nat := 1531775950482437251243373

theorem tailTrace_2983123 : CollatzResearch.WordTrace tailWord_2983123 prefixEnd_2983123 1531775950482437251243373 := by
  unfold tailWord_2983123
  simp only [CollatzResearch.WordTrace]
  refine ⟨108803434371662322691986023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72535622914441548461324015 108803434371662322691986023)
  ·
    refine ⟨163205151557493484037979035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108803434371662322691986023 163205151557493484037979035)
    ·
      refine ⟨244807727336240226056968553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163205151557493484037979035 244807727336240226056968553)
      ·
        refine ⟨183605795502180169542726415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244807727336240226056968553 183605795502180169542726415)
        ·
          refine ⟨275408693253270254314089623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183605795502180169542726415 275408693253270254314089623)
          ·
            refine ⟨413113039879905381471134435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275408693253270254314089623 413113039879905381471134435)
            ·
              refine ⟨619669559819858072206701653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413113039879905381471134435 619669559819858072206701653)
              ·
                refine ⟨7261752654138961783672285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 619669559819858072206701653 7261752654138961783672285)
                ·
                  refine ⟨2723157245302110668877107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7261752654138961783672285 2723157245302110668877107)
                  ·
                    refine ⟨4084735867953166003315661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2723157245302110668877107 4084735867953166003315661)
                    ·
                      refine ⟨1531775950482437251243373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4084735867953166003315661 1531775950482437251243373)
                      ·
                        rfl

theorem cell23_2983123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 1, 3].length) (baseStart_2983123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983123 prefixEnd_2983123 := by exact prefixLift 2983123
  have htrace : WordTrace (prefixWord ++ tailWord_2983123) baseStart_2983123 baseEnd_2983123 := by
    simpa [prefixWord, tailWord_2983123, baseEnd_2983123] using wordTrace_append hprefix tailTrace_2983123
  have hstable : (prefixWord ++ tailWord_2983123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983123).length < 2 ^ (prefixWord ++ tailWord_2983123).sum := by decide
  have hdescent : baseEnd_2983123 < baseStart_2983123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983124 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 2, 1, 4]
def baseStart_2983124 : Nat := 118140960795 + 2983124 * 2 ^ 59
def prefixEnd_2983124 : Nat := 4983230072969 + 3 ^ 40 * 2983124 * 2
def baseEnd_2983124 : Nat := 1531776463963091747330869

theorem tailTrace_2983124 : CollatzResearch.WordTrace tailWord_2983124 prefixEnd_2983124 1531776463963091747330869 := by
  unfold tailWord_2983124
  simp only [CollatzResearch.WordTrace]
  refine ⟨54401735422329349931386213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72535647229772466575181617 54401735422329349931386213)
  ·
    refine ⟨10200325391686753112134915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54401735422329349931386213 10200325391686753112134915)
    ·
      refine ⟨15300488087530129668202373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10200325391686753112134915 15300488087530129668202373)
      ·
        refine ⟨2868841516411899312787945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15300488087530129668202373 2868841516411899312787945)
        ·
          refine ⟨2151631137308924484590959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2868841516411899312787945 2151631137308924484590959)
          ·
            refine ⟨3227446705963386726886439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151631137308924484590959 3227446705963386726886439)
            ·
              refine ⟨4841170058945080090329659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3227446705963386726886439 4841170058945080090329659)
              ·
                refine ⟨7261755088417620135494489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4841170058945080090329659 7261755088417620135494489)
                ·
                  refine ⟨5446316316313215101620867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7261755088417620135494489 5446316316313215101620867)
                  ·
                    refine ⟨8169474474469822652431301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5446316316313215101620867 8169474474469822652431301)
                    ·
                      refine ⟨1531776463963091747330869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8169474474469822652431301 1531776463963091747330869)
                      ·
                        rfl

theorem cell23_2983124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_2983124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983124 prefixEnd_2983124 := by exact prefixLift 2983124
  have htrace : WordTrace (prefixWord ++ tailWord_2983124) baseStart_2983124 baseEnd_2983124 := by
    simpa [prefixWord, tailWord_2983124, baseEnd_2983124] using wordTrace_append hprefix tailTrace_2983124
  have hstable : (prefixWord ++ tailWord_2983124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983124).length < 2 ^ (prefixWord ++ tailWord_2983124).sum := by decide
  have hdescent : baseEnd_2983124 < baseStart_2983124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983150 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 2, 3, 2]
def baseStart_2983150 : Nat := 118140960795 + 2983150 * 2 ^ 59
def prefixEnd_2983150 : Nat := 4983230072969 + 3 ^ 40 * 2983150 * 2
def baseEnd_2983150 : Nat := 1531789814460108645605749

theorem tailTrace_2983150 : CollatzResearch.WordTrace tailWord_2983150 prefixEnd_2983150 1531789814460108645605749 := by
  unfold tailWord_2983150
  simp only [CollatzResearch.WordTrace]
  refine ⟨13600552392820563287902363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72536279428376337535479269 13600552392820563287902363)
  ·
    refine ⟨20400828589230844931853545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13600552392820563287902363 20400828589230844931853545)
    ·
      refine ⟨15300621441923133698890159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20400828589230844931853545 15300621441923133698890159)
      ·
        refine ⟨22950932162884700548335239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15300621441923133698890159 22950932162884700548335239)
        ·
          refine ⟨34426398244327050822502859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22950932162884700548335239 34426398244327050822502859)
          ·
            refine ⟨51639597366490576233754289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34426398244327050822502859 51639597366490576233754289)
            ·
              refine ⟨38729698024867932175315717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51639597366490576233754289 38729698024867932175315717)
              ·
                refine ⟨7261818379662737282871697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38729698024867932175315717 7261818379662737282871697)
                ·
                  refine ⟨5446363784747052962153773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7261818379662737282871697 5446363784747052962153773)
                  ·
                    refine ⟨2042386419280144860807665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5446363784747052962153773 2042386419280144860807665)
                    ·
                      refine ⟨1531789814460108645605749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2042386419280144860807665 1531789814460108645605749)
                      ·
                        rfl

theorem cell23_2983150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_2983150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983150 prefixEnd_2983150 := by exact prefixLift 2983150
  have htrace : WordTrace (prefixWord ++ tailWord_2983150) baseStart_2983150 baseEnd_2983150 := by
    simpa [prefixWord, tailWord_2983150, baseEnd_2983150] using wordTrace_append hprefix tailTrace_2983150
  have hstable : (prefixWord ++ tailWord_2983150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983150).length < 2 ^ (prefixWord ++ tailWord_2983150).sum := by decide
  have hdescent : baseEnd_2983150 < baseStart_2983150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983180 : List Nat := [2, 2, 1, 2, 2, 4, 2, 2, 1, 1, 4]
def baseStart_2983180 : Nat := 118140960795 + 2983180 * 2 ^ 59
def prefixEnd_2983180 : Nat := 4983230072969 + 3 ^ 40 * 2983180 * 2
def baseEnd_2983180 : Nat := 1531805218879743528230611

theorem tailTrace_2983180 : CollatzResearch.WordTrace tailWord_2983180 prefixEnd_2983180 1531805218879743528230611 := by
  unfold tailWord_2983180
  simp only [CollatzResearch.WordTrace]
  refine ⟨54402756666227910713405497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72537008888303880951207329 54402756666227910713405497)
  ·
    refine ⟨40802067499670933035054123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54402756666227910713405497 40802067499670933035054123)
    ·
      refine ⟨61203101249506399552581185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40802067499670933035054123 61203101249506399552581185)
      ·
        refine ⟨45902325937129799664435889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61203101249506399552581185 45902325937129799664435889)
        ·
          refine ⟨34426744452847349748326917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45902325937129799664435889 34426744452847349748326917)
          ·
            refine ⟨6455014584908878077811297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34426744452847349748326917 6455014584908878077811297)
            ·
              refine ⟨4841260938681658558358473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6455014584908878077811297 4841260938681658558358473)
              ·
                refine ⟨3630945704011243918768855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4841260938681658558358473 3630945704011243918768855)
                ·
                  refine ⟨5446418556016865878153283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3630945704011243918768855 5446418556016865878153283)
                  ·
                    refine ⟨8169627834025298817229925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5446418556016865878153283 8169627834025298817229925)
                    ·
                      refine ⟨1531805218879743528230611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8169627834025298817229925 1531805218879743528230611)
                      ·
                        rfl

theorem cell23_2983180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_2983180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983180 prefixEnd_2983180 := by exact prefixLift 2983180
  have htrace : WordTrace (prefixWord ++ tailWord_2983180) baseStart_2983180 baseEnd_2983180 := by
    simpa [prefixWord, tailWord_2983180, baseEnd_2983180] using wordTrace_append hprefix tailTrace_2983180
  have hstable : (prefixWord ++ tailWord_2983180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983180).length < 2 ^ (prefixWord ++ tailWord_2983180).sum := by decide
  have hdescent : baseEnd_2983180 < baseStart_2983180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983200 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 5]
def baseStart_2983200 : Nat := 118140960795 + 2983200 * 2 ^ 59
def prefixEnd_2983200 : Nat := 4983230072969 + 3 ^ 40 * 2983200 * 2
def baseEnd_2983200 : Nat := 1531815488492833449980519

theorem tailTrace_2983200 : CollatzResearch.WordTrace tailWord_2983200 prefixEnd_2983200 1531815488492833449980519 := by
  unfold tailWord_2983200
  simp only [CollatzResearch.WordTrace]
  refine ⟨54403121396191682421269527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72537495194922243228359369 54403121396191682421269527)
  ·
    refine ⟨81604682094287523631904291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54403121396191682421269527 81604682094287523631904291)
    ·
      refine ⟨122407023141431285447856437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81604682094287523631904291 122407023141431285447856437)
      ·
        refine ⟨11475658419509183010736541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122407023141431285447856437 11475658419509183010736541)
        ·
          refine ⟨4303371907315943629026203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11475658419509183010736541 4303371907315943629026203)
          ·
            refine ⟨6455057860973915443539305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4303371907315943629026203 6455057860973915443539305)
            ·
              refine ⟨4841293395730436582654479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6455057860973915443539305 4841293395730436582654479)
              ·
                refine ⟨7261940093595654873981719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4841293395730436582654479 7261940093595654873981719)
                ·
                  refine ⟨10892910140393482310972579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7261940093595654873981719 10892910140393482310972579)
                  ·
                    refine ⟨16339365210590223466458869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10892910140393482310972579 16339365210590223466458869)
                    ·
                      refine ⟨1531815488492833449980519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16339365210590223466458869 1531815488492833449980519)
                      ·
                        rfl

theorem cell23_2983200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_2983200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983200 prefixEnd_2983200 := by exact prefixLift 2983200
  have htrace : WordTrace (prefixWord ++ tailWord_2983200) baseStart_2983200 baseEnd_2983200 := by
    simpa [prefixWord, tailWord_2983200, baseEnd_2983200] using wordTrace_append hprefix tailTrace_2983200
  have hstable : (prefixWord ++ tailWord_2983200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983200).length < 2 ^ (prefixWord ++ tailWord_2983200).sum := by decide
  have hdescent : baseEnd_2983200 < baseStart_2983200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983216 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 2, 7]
def baseStart_2983216 : Nat := 118140960795 + 2983216 * 2 ^ 59
def prefixEnd_2983216 : Nat := 4983230072969 + 3 ^ 40 * 2983216 * 2
def baseEnd_2983216 : Nat := 510607901394435129126815

theorem tailTrace_2983216 : CollatzResearch.WordTrace tailWord_2983216 prefixEnd_2983216 510607901394435129126815 := by
  unfold tailWord_2983216
  simp only [CollatzResearch.WordTrace]
  refine ⟨54403413180162699787560751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72537884240216933050081001 54403413180162699787560751)
  ·
    refine ⟨81605119770244049681341127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54403413180162699787560751 81605119770244049681341127)
    ·
      refine ⟨122407679655366074522011691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81605119770244049681341127 122407679655366074522011691)
      ·
        refine ⟨183611519483049111783017537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122407679655366074522011691 183611519483049111783017537)
        ·
          refine ⟨137708639612286833837263153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183611519483049111783017537 137708639612286833837263153)
          ·
            refine ⟨103281479709215125377947365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137708639612286833837263153 103281479709215125377947365)
            ·
              refine ⟨19365277445477836008365131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103281479709215125377947365 19365277445477836008365131)
              ·
                refine ⟨29047916168216754012547697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19365277445477836008365131 29047916168216754012547697)
                ·
                  refine ⟨21785937126162565509410773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29047916168216754012547697 21785937126162565509410773)
                  ·
                    refine ⟨510607901394435129126815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21785937126162565509410773 510607901394435129126815)
                    ·
                      rfl

theorem cell23_2983216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 2, 7].length) (baseStart_2983216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983216 prefixEnd_2983216 := by exact prefixLift 2983216
  have htrace : WordTrace (prefixWord ++ tailWord_2983216) baseStart_2983216 baseEnd_2983216 := by
    simpa [prefixWord, tailWord_2983216, baseEnd_2983216] using wordTrace_append hprefix tailTrace_2983216
  have hstable : (prefixWord ++ tailWord_2983216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983216).length < 2 ^ (prefixWord ++ tailWord_2983216).sum := by decide
  have hdescent : baseEnd_2983216 < baseStart_2983216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983223 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 1, 9, 2]
def baseStart_2983223 : Nat := 118140960795 + 2983223 * 2 ^ 59
def prefixEnd_2983223 : Nat := 4983230072969 + 3 ^ 40 * 2983223 * 2
def baseEnd_2983223 : Nat := 1531827298547886859992913

theorem tailTrace_2983223 : CollatzResearch.WordTrace tailWord_2983223 prefixEnd_2983223 1531827298547886859992913 := by
  unfold tailWord_2983223
  simp only [CollatzResearch.WordTrace]
  refine ⟨108807081671300039770626323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72538054447533359847084215 108807081671300039770626323)
  ·
    refine ⟨163210622506950059655939485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108807081671300039770626323 163210622506950059655939485)
    ·
      refine ⟨61203983440106272370977307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163210622506950059655939485 61203983440106272370977307)
      ·
        refine ⟨91805975160159408556465961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61203983440106272370977307 91805975160159408556465961)
        ·
          refine ⟨68854481370119556417349471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91805975160159408556465961 68854481370119556417349471)
          ·
            refine ⟨103281722055179334626024207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68854481370119556417349471 103281722055179334626024207)
            ·
              refine ⟨154922583082769001939036311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103281722055179334626024207 154922583082769001939036311)
              ·
                refine ⟨232383874624153502908554467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154922583082769001939036311 232383874624153502908554467)
                ·
                  refine ⟨348575811936230254362831701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232383874624153502908554467 348575811936230254362831701)
                  ·
                    refine ⟨2042436398063849146657217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 348575811936230254362831701 2042436398063849146657217)
                    ·
                      refine ⟨1531827298547886859992913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2042436398063849146657217 1531827298547886859992913)
                      ·
                        rfl

theorem cell23_2983223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 9, 2].length) (baseStart_2983223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983223 prefixEnd_2983223 := by exact prefixLift 2983223
  have htrace : WordTrace (prefixWord ++ tailWord_2983223) baseStart_2983223 baseEnd_2983223 := by
    simpa [prefixWord, tailWord_2983223, baseEnd_2983223] using wordTrace_append hprefix tailTrace_2983223
  have hstable : (prefixWord ++ tailWord_2983223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983223).length < 2 ^ (prefixWord ++ tailWord_2983223).sum := by decide
  have hdescent : baseEnd_2983223 < baseStart_2983223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983230 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_2983230 : Nat := 118140960795 + 2983230 * 2 ^ 59
def prefixEnd_2983230 : Nat := 4983230072969 + 3 ^ 40 * 2983230 * 2
def baseEnd_2983230 : Nat := 1531830892912468332605381

theorem tailTrace_2983230 : CollatzResearch.WordTrace tailWord_2983230 prefixEnd_2983230 1531830892912468332605381 := by
  unfold tailWord_2983230
  simp only [CollatzResearch.WordTrace]
  refine ⟨13600917122784334995766393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72538224654849786644087429 13600917122784334995766393)
  ·
    refine ⟨10200687842088251246824795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13600917122784334995766393 10200687842088251246824795)
    ·
      refine ⟨15301031763132376870237193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10200687842088251246824795 15301031763132376870237193)
      ·
        refine ⟨11475773822349282652677895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15301031763132376870237193 11475773822349282652677895)
        ·
          refine ⟨17213660733523923979016843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11475773822349282652677895 17213660733523923979016843)
          ·
            refine ⟨25820491100285885968525265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17213660733523923979016843 25820491100285885968525265)
            ·
              refine ⟨19365368325214414476393949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25820491100285885968525265 19365368325214414476393949)
              ·
                refine ⟨7262013121955405428647731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19365368325214414476393949 7262013121955405428647731)
                ·
                  refine ⟨10893019682933108142971597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7262013121955405428647731 10893019682933108142971597)
                  ·
                    refine ⟨4084882381099915553614349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10893019682933108142971597 4084882381099915553614349)
                    ·
                      refine ⟨1531830892912468332605381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4084882381099915553614349 1531830892912468332605381)
                      ·
                        rfl

theorem cell23_2983230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_2983230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983230 prefixEnd_2983230 := by exact prefixLift 2983230
  have htrace : WordTrace (prefixWord ++ tailWord_2983230) baseStart_2983230 baseEnd_2983230 := by
    simpa [prefixWord, tailWord_2983230, baseEnd_2983230] using wordTrace_append hprefix tailTrace_2983230
  have hstable : (prefixWord ++ tailWord_2983230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983230).length < 2 ^ (prefixWord ++ tailWord_2983230).sum := by decide
  have hdescent : baseEnd_2983230 < baseStart_2983230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983254 : List Nat := [5, 2, 3, 1, 2, 10]
def baseStart_2983254 : Nat := 118140960795 + 2983254 * 2 ^ 59
def prefixEnd_2983254 : Nat := 4983230072969 + 3 ^ 40 * 2983254 * 2
def baseEnd_2983254 : Nat := 6303881549169449541997

theorem tailTrace_2983254 : CollatzResearch.WordTrace tailWord_2983254 prefixEnd_2983254 6303881549169449541997 := by
  unfold tailWord_2983254
  simp only [CollatzResearch.WordTrace]
  refine ⟨6800513270886733254062801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72538808222791821376669877 6800513270886733254062801)
  ·
    refine ⟨5100384953165049940547101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6800513270886733254062801 5100384953165049940547101)
    ·
      refine ⟨1912644357436893727705163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5100384953165049940547101 1912644357436893727705163)
      ·
        refine ⟨2868966536155340591557745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1912644357436893727705163 2868966536155340591557745)
        ·
          refine ⟨2151724902116505443668309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2868966536155340591557745 2151724902116505443668309)
          ·
            refine ⟨6303881549169449541997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2151724902116505443668309 6303881549169449541997)
            ·
              rfl

theorem cell23_2983254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 10].length) (baseStart_2983254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983254 prefixEnd_2983254 := by exact prefixLift 2983254
  have htrace : WordTrace (prefixWord ++ tailWord_2983254) baseStart_2983254 baseEnd_2983254 := by
    simpa [prefixWord, tailWord_2983254, baseEnd_2983254] using wordTrace_append hprefix tailTrace_2983254
  have hstable : (prefixWord ++ tailWord_2983254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983254).length < 2 ^ (prefixWord ++ tailWord_2983254).sum := by decide
  have hdescent : baseEnd_2983254 < baseStart_2983254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983287 : List Nat := [1, 1, 3, 1, 1, 2, 3, 5, 2, 2, 2]
def baseStart_2983287 : Nat := 118140960795 + 2983287 * 2 ^ 59
def prefixEnd_2983287 : Nat := 4983230072969 + 3 ^ 40 * 2983287 * 2
def baseEnd_2983287 : Nat := 1531860161309774609592619

theorem tailTrace_2983287 : CollatzResearch.WordTrace tailWord_2983287 prefixEnd_2983287 1531860161309774609592619 := by
  unfold tailWord_2983287
  simp only [CollatzResearch.WordTrace]
  refine ⟨108809415943068178700956115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72539610628712119133970743 108809415943068178700956115)
  ·
    refine ⟨163214123914602268051434173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108809415943068178700956115 163214123914602268051434173)
    ·
      refine ⟨61205296467975850519287815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163214123914602268051434173 61205296467975850519287815)
      ·
        refine ⟨91807944701963775778931723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61205296467975850519287815 91807944701963775778931723)
        ·
          refine ⟨137711917052945663668397585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91807944701963775778931723 137711917052945663668397585)
          ·
            refine ⟨103283937789709247751298189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137711917052945663668397585 103283937789709247751298189)
            ·
              refine ⟨38731476671140967906736821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103283937789709247751298189 38731476671140967906736821)
              ·
                refine ⟨3631075937919465741256577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38731476671140967906736821 3631075937919465741256577)
                ·
                  refine ⟨2723306953439599305942433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3631075937919465741256577 2723306953439599305942433)
                  ·
                    refine ⟨2042480215079699479456825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2723306953439599305942433 2042480215079699479456825)
                    ·
                      refine ⟨1531860161309774609592619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2042480215079699479456825 1531860161309774609592619)
                      ·
                        rfl

theorem cell23_2983287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 2, 2].length) (baseStart_2983287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983287 prefixEnd_2983287 := by exact prefixLift 2983287
  have htrace : WordTrace (prefixWord ++ tailWord_2983287) baseStart_2983287 baseEnd_2983287 := by
    simpa [prefixWord, tailWord_2983287, baseEnd_2983287] using wordTrace_append hprefix tailTrace_2983287
  have hstable : (prefixWord ++ tailWord_2983287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983287).length < 2 ^ (prefixWord ++ tailWord_2983287).sum := by decide
  have hdescent : baseEnd_2983287 < baseStart_2983287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983293 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 7]
def baseStart_2983293 : Nat := 118140960795 + 2983293 * 2 ^ 59
def prefixEnd_2983293 : Nat := 4983230072969 + 3 ^ 40 * 2983293 * 2
def baseEnd_2983293 : Nat := 170207026910411287346399

theorem tailTrace_2983293 : CollatzResearch.WordTrace tailWord_2983293 prefixEnd_2983293 170207026910411287346399 := by
  unfold tailWord_2983293
  simp only [CollatzResearch.WordTrace]
  refine ⟨108809634781046441725674533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72539756520697627817116355 108809634781046441725674533)
  ·
    refine ⟨20401806521446207823563975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108809634781046441725674533 20401806521446207823563975)
    ·
      refine ⟨30602709782169311735345963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20401806521446207823563975 30602709782169311735345963)
      ·
        refine ⟨45904064673253967603018945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30602709782169311735345963 45904064673253967603018945)
        ·
          refine ⟨34428048504940475702264209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45904064673253967603018945 34428048504940475702264209)
          ·
            refine ⟨25821036378705356776698157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34428048504940475702264209 25821036378705356776698157)
            ·
              refine ⟨9682888642014508791261809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25821036378705356776698157 9682888642014508791261809)
              ·
                refine ⟨7262166481510881593446357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9682888642014508791261809 7262166481510881593446357)
                ·
                  refine ⟨170207026910411287346399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7262166481510881593446357 170207026910411287346399)
                  ·
                    rfl

theorem cell23_2983293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_2983293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983293 prefixEnd_2983293 := by exact prefixLift 2983293
  have htrace : WordTrace (prefixWord ++ tailWord_2983293) baseStart_2983293 baseEnd_2983293 := by
    simpa [prefixWord, tailWord_2983293, baseEnd_2983293] using wordTrace_append hprefix tailTrace_2983293
  have hstable : (prefixWord ++ tailWord_2983293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983293).length < 2 ^ (prefixWord ++ tailWord_2983293).sum := by decide
  have hdescent : baseEnd_2983293 < baseStart_2983293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983360 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 1, 6, 2]
def baseStart_2983360 : Nat := 118140960795 + 2983360 * 2 ^ 59
def prefixEnd_2983360 : Nat := 4983230072969 + 3 ^ 40 * 2983360 * 2
def baseEnd_2983360 : Nat := 1531897645397552823979783

theorem tailTrace_2983360 : CollatzResearch.WordTrace tailWord_2983360 prefixEnd_2983360 1531897645397552823979783 := by
  unfold tailWord_2983360
  simp only [CollatzResearch.WordTrace]
  refine ⟨54406039235901856084181767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72541385647869141445575689 54406039235901856084181767)
  ·
    refine ⟨81609058853852784126272651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54406039235901856084181767 81609058853852784126272651)
    ·
      refine ⟨122413588280779176189408977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81609058853852784126272651 122413588280779176189408977)
      ·
        refine ⟨91810191210584382142056733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122413588280779176189408977 91810191210584382142056733)
        ·
          refine ⟨34428821703969143303271275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91810191210584382142056733 34428821703969143303271275)
          ·
            refine ⟨51643232555953714954906913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34428821703969143303271275 51643232555953714954906913)
            ·
              refine ⟨38732424416965286216180185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51643232555953714954906913 38732424416965286216180185)
              ·
                refine ⟨29049318312723964662135139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38732424416965286216180185 29049318312723964662135139)
                ·
                  refine ⟨43573977469085946993202709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29049318312723964662135139 43573977469085946993202709)
                  ·
                    refine ⟨2042530193863403765306377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43573977469085946993202709 2042530193863403765306377)
                    ·
                      refine ⟨1531897645397552823979783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2042530193863403765306377 1531897645397552823979783)
                      ·
                        rfl

theorem cell23_2983360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 6, 2].length) (baseStart_2983360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983360 prefixEnd_2983360 := by exact prefixLift 2983360
  have htrace : WordTrace (prefixWord ++ tailWord_2983360) baseStart_2983360 baseEnd_2983360 := by
    simpa [prefixWord, tailWord_2983360, baseEnd_2983360] using wordTrace_append hprefix tailTrace_2983360
  have hstable : (prefixWord ++ tailWord_2983360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983360).length < 2 ^ (prefixWord ++ tailWord_2983360).sum := by decide
  have hdescent : baseEnd_2983360 < baseStart_2983360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983400 : List Nat := [2, 1, 4, 1, 1, 2, 3, 3, 6]
def baseStart_2983400 : Nat := 118140960795 + 2983400 * 2 ^ 59
def prefixEnd_2983400 : Nat := 4983230072969 + 3 ^ 40 * 2983400 * 2
def baseEnd_2983400 : Nat := 170213131624859185275511

theorem tailTrace_2983400 : CollatzResearch.WordTrace tailWord_2983400 prefixEnd_2983400 170213131624859185275511 := by
  unfold tailWord_2983400
  simp only [CollatzResearch.WordTrace]
  refine ⟨54406768695829399499909827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72542358261105865999879769 54406768695829399499909827)
  ·
    refine ⟨81610153043744099249864741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54406768695829399499909827 81610153043744099249864741)
    ·
      refine ⟨15301903695702018609349639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81610153043744099249864741 15301903695702018609349639)
      ·
        refine ⟨22952855543553027914024459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15301903695702018609349639 22952855543553027914024459)
        ·
          refine ⟨34429283315329541871036689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22952855543553027914024459 34429283315329541871036689)
          ·
            refine ⟨25821962486497156403277517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34429283315329541871036689 25821962486497156403277517)
            ·
              refine ⟨9683235932436433651229069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25821962486497156403277517 9683235932436433651229069)
              ·
                refine ⟨3631213474663662619210901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9683235932436433651229069 3631213474663662619210901)
                ·
                  refine ⟨170213131624859185275511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3631213474663662619210901 170213131624859185275511)
                  ·
                    rfl

theorem cell23_2983400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 6].length) (baseStart_2983400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983400 prefixEnd_2983400 := by exact prefixLift 2983400
  have htrace : WordTrace (prefixWord ++ tailWord_2983400) baseStart_2983400 baseEnd_2983400 := by
    simpa [prefixWord, tailWord_2983400, baseEnd_2983400] using wordTrace_append hprefix tailTrace_2983400
  have hstable : (prefixWord ++ tailWord_2983400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983400).length < 2 ^ (prefixWord ++ tailWord_2983400).sum := by decide
  have hdescent : baseEnd_2983400 < baseStart_2983400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983414 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_2983414 : Nat := 118140960795 + 2983414 * 2 ^ 59
def prefixEnd_2983414 : Nat := 4983230072969 + 3 ^ 40 * 2983414 * 2
def baseEnd_2983414 : Nat := 1531925373352895612704535

theorem tailTrace_2983414 : CollatzResearch.WordTrace tailWord_2983414 prefixEnd_2983414 1531925373352895612704535 := by
  unfold tailWord_2983414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6800878000850504961926831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72542698675738719593886197 6800878000850504961926831)
  ·
    refine ⟨10201317001275757442890247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6800878000850504961926831 10201317001275757442890247)
    ·
      refine ⟨15301975501913636164335371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10201317001275757442890247 15301975501913636164335371)
      ·
        refine ⟨22952963252870454246503057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15301975501913636164335371 22952963252870454246503057)
        ·
          refine ⟨17214722439652840684877293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22952963252870454246503057 17214722439652840684877293)
          ·
            refine ⟨6455520914869815256828985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17214722439652840684877293 6455520914869815256828985)
            ·
              refine ⟨4841640686152361442621739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6455520914869815256828985 4841640686152361442621739)
              ·
                refine ⟨7262461029228542163932609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4841640686152361442621739 7262461029228542163932609)
                ·
                  refine ⟨5446845771921406622949457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7262461029228542163932609 5446845771921406622949457)
                  ·
                    refine ⟨4085134328941054967212093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5446845771921406622949457 4085134328941054967212093)
                    ·
                      refine ⟨1531925373352895612704535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4085134328941054967212093 1531925373352895612704535)
                      ·
                        rfl

theorem cell23_2983414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_2983414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983414 prefixEnd_2983414 := by exact prefixLift 2983414
  have htrace : WordTrace (prefixWord ++ tailWord_2983414) baseStart_2983414 baseEnd_2983414 := by
    simpa [prefixWord, tailWord_2983414, baseEnd_2983414] using wordTrace_append hprefix tailTrace_2983414
  have hstable : (prefixWord ++ tailWord_2983414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983414).length < 2 ^ (prefixWord ++ tailWord_2983414).sum := by decide
  have hdescent : baseEnd_2983414 < baseStart_2983414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983423 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 5]
def baseStart_2983423 : Nat := 118140960795 + 2983423 * 2 ^ 59
def prefixEnd_2983423 : Nat := 4983230072969 + 3 ^ 40 * 2983423 * 2
def baseEnd_2983423 : Nat := 1531929994678786077491993

theorem tailTrace_2983423 : CollatzResearch.WordTrace tailWord_2983423 prefixEnd_2983423 1531929994678786077491993 := by
  unfold tailWord_2983423
  simp only [CollatzResearch.WordTrace]
  refine ⟨108814376270575473927906923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72542917513716982618604615 108814376270575473927906923)
  ·
    refine ⟨163221564405863210891860385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108814376270575473927906923 163221564405863210891860385)
    ·
      refine ⟨122416173304397408168895289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163221564405863210891860385 122416173304397408168895289)
      ·
        refine ⟨91812129978298056126671467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122416173304397408168895289 91812129978298056126671467)
        ·
          refine ⟨137718194967447084190007201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91812129978298056126671467 137718194967447084190007201)
          ·
            refine ⟨103288646225585313142505401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137718194967447084190007201 103288646225585313142505401)
            ·
              refine ⟨77466484669188984856879051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103288646225585313142505401 77466484669188984856879051)
              ·
                refine ⟨116199727003783477285318577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77466484669188984856879051 116199727003783477285318577)
                ·
                  refine ⟨87149795252837607963988933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116199727003783477285318577 87149795252837607963988933)
                  ·
                    refine ⟨16340586609907051493247925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87149795252837607963988933 16340586609907051493247925)
                    ·
                      refine ⟨1531929994678786077491993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16340586609907051493247925 1531929994678786077491993)
                      ·
                        rfl

theorem cell23_2983423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_2983423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983423 prefixEnd_2983423 := by exact prefixLift 2983423
  have htrace : WordTrace (prefixWord ++ tailWord_2983423) baseStart_2983423 baseEnd_2983423 := by
    simpa [prefixWord, tailWord_2983423, baseEnd_2983423] using wordTrace_append hprefix tailTrace_2983423
  have hstable : (prefixWord ++ tailWord_2983423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983423).length < 2 ^ (prefixWord ++ tailWord_2983423).sum := by decide
  have hdescent : baseEnd_2983423 < baseStart_2983423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983438 : List Nat := [4, 1, 1, 2, 4, 2, 2, 2, 1, 4]
def baseStart_2983438 : Nat := 118140960795 + 2983438 * 2 ^ 59
def prefixEnd_2983438 : Nat := 4983230072969 + 3 ^ 40 * 2983438 * 2
def baseEnd_2983438 : Nat := 510645898962867839601475

theorem tailTrace_2983438 : CollatzResearch.WordTrace tailWord_2983438 prefixEnd_2983438 510645898962867839601475 := by
  unfold tailWord_2983438
  simp only [CollatzResearch.WordTrace]
  refine ⟨13601865420690141436212871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72543282243680754326468645 13601865420690141436212871)
  ·
    refine ⟨20402798131035212154319307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13601865420690141436212871 20402798131035212154319307)
    ·
      refine ⟨30604197196552818231478961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20402798131035212154319307 30604197196552818231478961)
      ·
        refine ⟨22953147897414613673609221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30604197196552818231478961 22953147897414613673609221)
        ·
          refine ⟨4303715230765240063801729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22953147897414613673609221 4303715230765240063801729)
          ·
            refine ⟨3227786423073930047851297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4303715230765240063801729 3227786423073930047851297)
            ·
              refine ⟨2420839817305447535888473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3227786423073930047851297 2420839817305447535888473)
              ·
                refine ⟨1815629862979085651916355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2420839817305447535888473 1815629862979085651916355)
                ·
                  refine ⟨2723444794468628477874533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1815629862979085651916355 2723444794468628477874533)
                  ·
                    refine ⟨510645898962867839601475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2723444794468628477874533 510645898962867839601475)
                    ·
                      rfl

theorem cell23_2983438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_2983438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983438 prefixEnd_2983438 := by exact prefixLift 2983438
  have htrace : WordTrace (prefixWord ++ tailWord_2983438) baseStart_2983438 baseEnd_2983438 := by
    simpa [prefixWord, tailWord_2983438, baseEnd_2983438] using wordTrace_append hprefix tailTrace_2983438
  have hstable : (prefixWord ++ tailWord_2983438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983438).length < 2 ^ (prefixWord ++ tailWord_2983438).sum := by decide
  have hdescent : baseEnd_2983438 < baseStart_2983438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983484 : List Nat := [2, 2, 2, 2, 4, 1, 1, 3, 1, 1, 4]
def baseStart_2983484 : Nat := 118140960795 + 2983484 * 2 ^ 59
def prefixEnd_2983484 : Nat := 4983230072969 + 3 ^ 40 * 2983484 * 2
def baseEnd_2983484 : Nat := 1531961316998710338829213

theorem tailTrace_2983484 : CollatzResearch.WordTrace tailWord_2983484 prefixEnd_2983484 1531961316998710338829213 := by
  unfold tailWord_2983484
  simp only [CollatzResearch.WordTrace]
  refine ⟨54408300561677240672938753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72544400748902987563918337 54408300561677240672938753)
  ·
    refine ⟨40806225421257930504704065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54408300561677240672938753 40806225421257930504704065)
    ·
      refine ⟨30604669065943447878528049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40806225421257930504704065 30604669065943447878528049)
      ·
        refine ⟨22953501799457585908896037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30604669065943447878528049 22953501799457585908896037)
        ·
          refine ⟨4303781587398297357918007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22953501799457585908896037 4303781587398297357918007)
          ·
            refine ⟨6455672381097446036877011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4303781587398297357918007 6455672381097446036877011)
            ·
              refine ⟨9683508571646169055315517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6455672381097446036877011 9683508571646169055315517)
              ·
                refine ⟨3631315714367313395743319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9683508571646169055315517 3631315714367313395743319)
                ·
                  refine ⟨5446973571550970093614979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3631315714367313395743319 5446973571550970093614979)
                  ·
                    refine ⟨8170460357326455140422469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5446973571550970093614979 8170460357326455140422469)
                    ·
                      refine ⟨1531961316998710338829213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8170460357326455140422469 1531961316998710338829213)
                      ·
                        rfl

theorem cell23_2983484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_2983484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983484 prefixEnd_2983484 := by exact prefixLift 2983484
  have htrace : WordTrace (prefixWord ++ tailWord_2983484) baseStart_2983484 baseEnd_2983484 := by
    simpa [prefixWord, tailWord_2983484, baseEnd_2983484] using wordTrace_append hprefix tailTrace_2983484
  have hstable : (prefixWord ++ tailWord_2983484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983484).length < 2 ^ (prefixWord ++ tailWord_2983484).sum := by decide
  have hdescent : baseEnd_2983484 < baseStart_2983484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983618 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_2983618 : Nat := 118140960795 + 2983618 * 2 ^ 59
def prefixEnd_2983618 : Nat := 4983230072969 + 3 ^ 40 * 2983618 * 2
def baseEnd_2983618 : Nat := 510676707802137604851199

theorem tailTrace_2983618 : CollatzResearch.WordTrace tailWord_2983618 prefixEnd_2983618 510676707802137604851199 := by
  unfold tailWord_2983618
  simp only [CollatzResearch.WordTrace]
  refine ⟨27205372126217255557813877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72547659003246014820837005 27205372126217255557813877)
  ·
    refine ⟨2550503636832867708545051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27205372126217255557813877 2550503636832867708545051)
    ·
      refine ⟨3825755455249301562817577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2550503636832867708545051 3825755455249301562817577)
      ·
        refine ⟨2869316591436976172113183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3825755455249301562817577 2869316591436976172113183)
        ·
          refine ⟨4303974887155464258169775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2869316591436976172113183 4303974887155464258169775)
          ·
            refine ⟨6455962330733196387254663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4303974887155464258169775 6455962330733196387254663)
            ·
              refine ⟨9683943496099794580881995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6455962330733196387254663 9683943496099794580881995)
              ·
                refine ⟨14525915244149691871322993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9683943496099794580881995 14525915244149691871322993)
                ·
                  refine ⟨10894436433112268903492245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14525915244149691871322993 10894436433112268903492245)
                  ·
                    refine ⟨510676707802137604851199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10894436433112268903492245 510676707802137604851199)
                    ·
                      rfl

theorem cell23_2983618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_2983618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983618 prefixEnd_2983618 := by exact prefixLift 2983618
  have htrace : WordTrace (prefixWord ++ tailWord_2983618) baseStart_2983618 baseEnd_2983618 := by
    simpa [prefixWord, tailWord_2983618, baseEnd_2983618] using wordTrace_append hprefix tailTrace_2983618
  have hstable : (prefixWord ++ tailWord_2983618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983618).length < 2 ^ (prefixWord ++ tailWord_2983618).sum := by decide
  have hdescent : baseEnd_2983618 < baseStart_2983618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983647 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 4]
def baseStart_2983647 : Nat := 118140960795 + 2983647 * 2 ^ 59
def prefixEnd_2983647 : Nat := 4983230072969 + 3 ^ 40 * 2983647 * 2
def baseEnd_2983647 : Nat := 1532045014345393201090963

theorem tailTrace_2983647 : CollatzResearch.WordTrace tailWord_2983647 prefixEnd_2983647 1532045014345393201090963 := by
  unfold tailWord_2983647
  simp only [CollatzResearch.WordTrace]
  refine ⟨108822546221763960184061195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72548364147842640122707463 108822546221763960184061195)
  ·
    refine ⟨163233819332645940276091793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108822546221763960184061195 163233819332645940276091793)
    ·
      refine ⟨122425364499484455207068845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163233819332645940276091793 122425364499484455207068845)
      ·
        refine ⟨45909511687306670702650817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122425364499484455207068845 45909511687306670702650817)
        ·
          refine ⟨34432133765480003026988113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45909511687306670702650817 34432133765480003026988113)
          ·
            refine ⟨25824100324110002270241085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34432133765480003026988113 25824100324110002270241085)
            ·
              refine ⟨9684037621541250851340407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25824100324110002270241085 9684037621541250851340407)
              ·
                refine ⟨14526056432311876277010611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9684037621541250851340407 14526056432311876277010611)
                ·
                  refine ⟨21789084648467814415515917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14526056432311876277010611 21789084648467814415515917)
                  ·
                    refine ⟨8170906743175430405818469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21789084648467814415515917 8170906743175430405818469)
                    ·
                      refine ⟨1532045014345393201090963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8170906743175430405818469 1532045014345393201090963)
                      ·
                        rfl

theorem cell23_2983647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_2983647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983647 prefixEnd_2983647 := by exact prefixLift 2983647
  have htrace : WordTrace (prefixWord ++ tailWord_2983647) baseStart_2983647 baseEnd_2983647 := by
    simpa [prefixWord, tailWord_2983647, baseEnd_2983647] using wordTrace_append hprefix tailTrace_2983647
  have hstable : (prefixWord ++ tailWord_2983647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983647).length < 2 ^ (prefixWord ++ tailWord_2983647).sum := by decide
  have hdescent : baseEnd_2983647 < baseStart_2983647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983657 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 7, 4]
def baseStart_2983657 : Nat := 118140960795 + 2983657 * 2 ^ 59
def prefixEnd_2983657 : Nat := 4983230072969 + 3 ^ 40 * 2983657 * 2
def baseEnd_2983657 : Nat := 510683383050646053988639

theorem tailTrace_2983657 : CollatzResearch.WordTrace tailWord_2983657 prefixEnd_2983657 510683383050646053988639 := by
  unfold tailWord_2983657
  simp only [CollatzResearch.WordTrace]
  refine ⟨108822910951727731891925225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72548607301151821261283483 108822910951727731891925225)
  ·
    refine ⟨81617183213795798918943919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108822910951727731891925225 81617183213795798918943919)
    ·
      refine ⟨122425774820693698378415879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81617183213795798918943919 122425774820693698378415879)
      ·
        refine ⟨183638662231040547567623819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122425774820693698378415879 183638662231040547567623819)
        ·
          refine ⟨275457993346560821351435729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183638662231040547567623819 275457993346560821351435729)
          ·
            refine ⟨206593495009920616013576797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275457993346560821351435729 206593495009920616013576797)
            ·
              refine ⟨77472560628720231005091299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206593495009920616013576797 77472560628720231005091299)
              ·
                refine ⟨116208840943080346507636949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77472560628720231005091299 116208840943080346507636949)
                ·
                  refine ⟨2723644709603445621272741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 116208840943080346507636949 2723644709603445621272741)
                  ·
                    refine ⟨510683383050646053988639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2723644709603445621272741 510683383050646053988639)
                    ·
                      rfl

theorem cell23_2983657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 4].length) (baseStart_2983657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983657 prefixEnd_2983657 := by exact prefixLift 2983657
  have htrace : WordTrace (prefixWord ++ tailWord_2983657) baseStart_2983657 baseEnd_2983657 := by
    simpa [prefixWord, tailWord_2983657, baseEnd_2983657] using wordTrace_append hprefix tailTrace_2983657
  have hstable : (prefixWord ++ tailWord_2983657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983657).length < 2 ^ (prefixWord ++ tailWord_2983657).sum := by decide
  have hdescent : baseEnd_2983657 < baseStart_2983657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983684 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_2983684 : Nat := 118140960795 + 2983684 * 2 ^ 59
def prefixEnd_2983684 : Nat := 4983230072969 + 3 ^ 40 * 2983684 * 2
def baseEnd_2983684 : Nat := 1532064013129609556328293

theorem tailTrace_2983684 : CollatzResearch.WordTrace tailWord_2983684 prefixEnd_2983684 1532064013129609556328293 := by
  unfold tailWord_2983684
  simp only [CollatzResearch.WordTrace]
  refine ⟨54411947861314957751579053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72549263815086610335438737 54411947861314957751579053)
  ·
    refine ⟨20404480447993109156842145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54411947861314957751579053 20404480447993109156842145)
    ·
      refine ⟨15303360335994831867631609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20404480447993109156842145 15303360335994831867631609)
      ·
        refine ⟨11477520251996123900723707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15303360335994831867631609 11477520251996123900723707)
        ·
          refine ⟨17216280377994185851085561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11477520251996123900723707 17216280377994185851085561)
          ·
            refine ⟨12912210283495639388314171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17216280377994185851085561 12912210283495639388314171)
            ·
              refine ⟨19368315425243459082471257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12912210283495639388314171 19368315425243459082471257)
              ·
                refine ⟨14526236568932594311853443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19368315425243459082471257 14526236568932594311853443)
                ·
                  refine ⟨21789354853398891467780165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14526236568932594311853443 21789354853398891467780165)
                  ·
                    refine ⟨4085504035012292150208781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21789354853398891467780165 4085504035012292150208781)
                    ·
                      refine ⟨1532064013129609556328293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4085504035012292150208781 1532064013129609556328293)
                      ·
                        rfl

theorem cell23_2983684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_2983684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983684 prefixEnd_2983684 := by exact prefixLift 2983684
  have htrace : WordTrace (prefixWord ++ tailWord_2983684) baseStart_2983684 baseEnd_2983684 := by
    simpa [prefixWord, tailWord_2983684, baseEnd_2983684] using wordTrace_append hprefix tailTrace_2983684
  have hstable : (prefixWord ++ tailWord_2983684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983684).length < 2 ^ (prefixWord ++ tailWord_2983684).sum := by decide
  have hdescent : baseEnd_2983684 < baseStart_2983684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983697 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 3]
def baseStart_2983697 : Nat := 118140960795 + 2983697 * 2 ^ 59
def prefixEnd_2983697 : Nat := 4983230072969 + 3 ^ 40 * 2983697 * 2
def baseEnd_2983697 : Nat := 1532070688378118005465733

theorem tailTrace_2983697 : CollatzResearch.WordTrace tailWord_2983697 prefixEnd_2983697 1532070688378118005465733 := by
  unfold tailWord_2983697
  simp only [CollatzResearch.WordTrace]
  refine ⟨108824369871582818723381345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72549579914388545815587563 108824369871582818723381345)
  ·
    refine ⟨81618277403687114042536009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108824369871582818723381345 81618277403687114042536009)
    ·
      refine ⟨61213708052765335531902007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81618277403687114042536009 61213708052765335531902007)
      ·
        refine ⟨91820562079148003297853011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61213708052765335531902007 91820562079148003297853011)
        ·
          refine ⟨137730843118722004946779517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91820562079148003297853011 137730843118722004946779517)
          ·
            refine ⟨51649066169520751855042319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137730843118722004946779517 51649066169520751855042319)
            ·
              refine ⟨77473599254281127782563479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51649066169520751855042319 77473599254281127782563479)
              ·
                refine ⟨116210398881421691673845219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77473599254281127782563479 116210398881421691673845219)
                ·
                  refine ⟨174315598322132537510767829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116210398881421691673845219 174315598322132537510767829)
                  ·
                    refine ⟨4085521835674981347908621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 174315598322132537510767829 4085521835674981347908621)
                    ·
                      refine ⟨1532070688378118005465733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4085521835674981347908621 1532070688378118005465733)
                      ·
                        rfl

theorem cell23_2983697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_2983697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983697 prefixEnd_2983697 := by exact prefixLift 2983697
  have htrace : WordTrace (prefixWord ++ tailWord_2983697) baseStart_2983697 baseEnd_2983697 := by
    simpa [prefixWord, tailWord_2983697, baseEnd_2983697] using wordTrace_append hprefix tailTrace_2983697
  have hstable : (prefixWord ++ tailWord_2983697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983697).length < 2 ^ (prefixWord ++ tailWord_2983697).sum := by decide
  have hdescent : baseEnd_2983697 < baseStart_2983697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983754 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_2983754 : Nat := 118140960795 + 2983754 * 2 ^ 59
def prefixEnd_2983754 : Nat := 4983230072969 + 3 ^ 40 * 2983754 * 2
def baseEnd_2983754 : Nat := 1532099956775424282452971

theorem tailTrace_2983754 : CollatzResearch.WordTrace tailWord_2983754 prefixEnd_2983754 1532099956775424282452971 := by
  unfold tailWord_2983754
  simp only [CollatzResearch.WordTrace]
  refine ⟨27206612208094079364551579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72550965888250878305470877 27206612208094079364551579)
  ·
    refine ⟨40809918312141119046827369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27206612208094079364551579 40809918312141119046827369)
    ·
      refine ⟨30607438734105839285120527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40809918312141119046827369 30607438734105839285120527)
      ·
        refine ⟨45911158101158758927680791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30607438734105839285120527 45911158101158758927680791)
        ·
          refine ⟨68866737151738138391521187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45911158101158758927680791 68866737151738138391521187)
          ·
            refine ⟨103300105727607207587281781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68866737151738138391521187 103300105727607207587281781)
            ·
              refine ⟨9684384911963175711307667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103300105727607207587281781 9684384911963175711307667)
              ·
                refine ⟨14526577367944763566961501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9684384911963175711307667 14526577367944763566961501)
                ·
                  refine ⟨5447466512979286337610563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14526577367944763566961501 5447466512979286337610563)
                  ·
                    refine ⟨8171199769468929506415845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5447466512979286337610563 8171199769468929506415845)
                    ·
                      refine ⟨1532099956775424282452971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8171199769468929506415845 1532099956775424282452971)
                      ·
                        rfl

theorem cell23_2983754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_2983754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983754 prefixEnd_2983754 := by exact prefixLift 2983754
  have htrace : WordTrace (prefixWord ++ tailWord_2983754) baseStart_2983754 baseEnd_2983754 := by
    simpa [prefixWord, tailWord_2983754, baseEnd_2983754] using wordTrace_append hprefix tailTrace_2983754
  have hstable : (prefixWord ++ tailWord_2983754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983754).length < 2 ^ (prefixWord ++ tailWord_2983754).sum := by decide
  have hdescent : baseEnd_2983754 < baseStart_2983754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983764 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_2983764 : Nat := 118140960795 + 2983764 * 2 ^ 59
def prefixEnd_2983764 : Nat := 4983230072969 + 3 ^ 40 * 2983764 * 2
def baseEnd_2983764 : Nat := 510701697193989747775975

theorem tailTrace_2983764 : CollatzResearch.WordTrace tailWord_2983764 prefixEnd_2983764 510701697193989747775975 := by
  unfold tailWord_2983764
  simp only [CollatzResearch.WordTrace]
  refine ⟨54413406781170044583035173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72551209041560059444046897 54413406781170044583035173)
  ·
    refine ⟨10202513771469383359319095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54413406781170044583035173 10202513771469383359319095)
    ·
      refine ⟨15303770657204075038978643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10202513771469383359319095 15303770657204075038978643)
      ·
        refine ⟨22955655985806112558467965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15303770657204075038978643 22955655985806112558467965)
        ·
          refine ⟨8608370994677292209425487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22955655985806112558467965 8608370994677292209425487)
          ·
            refine ⟨12912556492015938314138231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8608370994677292209425487 12912556492015938314138231)
            ·
              refine ⟨19368834738023907471207347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12912556492015938314138231 19368834738023907471207347)
              ·
                refine ⟨29053252107035861206811021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19368834738023907471207347 29053252107035861206811021)
                ·
                  refine ⟨10894969540138447952554133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29053252107035861206811021 10894969540138447952554133)
                  ·
                    refine ⟨510701697193989747775975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10894969540138447952554133 510701697193989747775975)
                    ·
                      rfl

theorem cell23_2983764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_2983764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983764 prefixEnd_2983764 := by exact prefixLift 2983764
  have htrace : WordTrace (prefixWord ++ tailWord_2983764) baseStart_2983764 baseEnd_2983764 := by
    simpa [prefixWord, tailWord_2983764, baseEnd_2983764] using wordTrace_append hprefix tailTrace_2983764
  have hstable : (prefixWord ++ tailWord_2983764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983764).length < 2 ^ (prefixWord ++ tailWord_2983764).sum := by decide
  have hdescent : baseEnd_2983764 < baseStart_2983764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983784 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2983784 : Nat := 118140960795 + 2983784 * 2 ^ 59
def prefixEnd_2983784 : Nat := 4983230072969 + 3 ^ 40 * 2983784 * 2
def baseEnd_2983784 : Nat := 1532115361195059165077833

theorem tailTrace_2983784 : CollatzResearch.WordTrace tailWord_2983784 prefixEnd_2983784 1532115361195059165077833 := by
  unfold tailWord_2983784
  simp only [CollatzResearch.WordTrace]
  refine ⟨54413771511133816290899203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72551695348178421721198937 54413771511133816290899203)
  ·
    refine ⟨81620657266700724436348805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54413771511133816290899203 81620657266700724436348805)
    ·
      refine ⟨15303873237506385831815401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81620657266700724436348805 15303873237506385831815401)
      ·
        refine ⟨11477904928129789373861551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15303873237506385831815401 11477904928129789373861551)
        ·
          refine ⟨17216857392194684060792327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11477904928129789373861551 17216857392194684060792327)
          ·
            refine ⟨25825286088292026091188491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17216857392194684060792327 25825286088292026091188491)
            ·
              refine ⟨38737929132438039136782737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25825286088292026091188491 38737929132438039136782737)
              ·
                refine ⟨29053446849328529352587053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38737929132438039136782737 29053446849328529352587053)
                ·
                  refine ⟨10895042568498198507220145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29053446849328529352587053 10895042568498198507220145)
                  ·
                    refine ⟨8171281926373648880415109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10895042568498198507220145 8171281926373648880415109)
                    ·
                      refine ⟨1532115361195059165077833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8171281926373648880415109 1532115361195059165077833)
                      ·
                        rfl

theorem cell23_2983784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2983784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983784 prefixEnd_2983784 := by exact prefixLift 2983784
  have htrace : WordTrace (prefixWord ++ tailWord_2983784) baseStart_2983784 baseEnd_2983784 := by
    simpa [prefixWord, tailWord_2983784, baseEnd_2983784] using wordTrace_append hprefix tailTrace_2983784
  have hstable : (prefixWord ++ tailWord_2983784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983784).length < 2 ^ (prefixWord ++ tailWord_2983784).sum := by decide
  have hdescent : baseEnd_2983784 < baseStart_2983784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983798 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_2983798 : Nat := 118140960795 + 2983798 * 2 ^ 59
def prefixEnd_2983798 : Nat := 4983230072969 + 3 ^ 40 * 2983798 * 2
def baseEnd_2983798 : Nat := 510707516641407370100923

theorem tailTrace_2983798 : CollatzResearch.WordTrace tailWord_2983798 prefixEnd_2983798 510707516641407370100923 := by
  unfold tailWord_2983798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6801753352763557060800503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72552035762811275315205365 6801753352763557060800503)
  ·
    refine ⟨10202630029145335591200755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6801753352763557060800503 10202630029145335591200755)
    ·
      refine ⟨15303945043718003386801133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10202630029145335591200755 15303945043718003386801133)
      ·
        refine ⟨5738979391394251270050425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15303945043718003386801133 5738979391394251270050425)
        ·
          refine ⟨4304234543545688452537819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5738979391394251270050425 4304234543545688452537819)
          ·
            refine ⟨6456351815318532678806729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304234543545688452537819 6456351815318532678806729)
            ·
              refine ⟨4842263861488899509105047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6456351815318532678806729 4842263861488899509105047)
              ·
                refine ⟨7263395792233349263657571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4842263861488899509105047 7263395792233349263657571)
                ·
                  refine ⟨10895093688350023895486357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7263395792233349263657571 10895093688350023895486357)
                  ·
                    refine ⟨510707516641407370100923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10895093688350023895486357 510707516641407370100923)
                    ·
                      rfl

theorem cell23_2983798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_2983798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983798 prefixEnd_2983798 := by exact prefixLift 2983798
  have htrace : WordTrace (prefixWord ++ tailWord_2983798) baseStart_2983798 baseEnd_2983798 := by
    simpa [prefixWord, tailWord_2983798, baseEnd_2983798] using wordTrace_append hprefix tailTrace_2983798
  have hstable : (prefixWord ++ tailWord_2983798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983798).length < 2 ^ (prefixWord ++ tailWord_2983798).sum := by decide
  have hdescent : baseEnd_2983798 < baseStart_2983798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983807 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 4, 7]
def baseStart_2983807 : Nat := 118140960795 + 2983807 * 2 ^ 59
def prefixEnd_2983807 : Nat := 4983230072969 + 3 ^ 40 * 2983807 * 2
def baseEnd_2983807 : Nat := 510709057083370858363409

theorem tailTrace_2983807 : CollatzResearch.WordTrace tailWord_2983807 prefixEnd_2983807 510709057083370858363409 := by
  unfold tailWord_2983807
  simp only [CollatzResearch.WordTrace]
  refine ⟨108828381901184307509885675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72552254600789538339923783 108828381901184307509885675)
  ·
    refine ⟨163242572851776461264828513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108828381901184307509885675 163242572851776461264828513)
    ·
      refine ⟨122431929638832345948621385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163242572851776461264828513 122431929638832345948621385)
      ·
        refine ⟨91823947229124259461466039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122431929638832345948621385 91823947229124259461466039)
        ·
          refine ⟨137735920843686389192199059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91823947229124259461466039 137735920843686389192199059)
          ·
            refine ⟨206603881265529583788298589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137735920843686389192199059 206603881265529583788298589)
            ·
              refine ⟨77476455474573593920611971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206603881265529583788298589 77476455474573593920611971)
              ·
                refine ⟨116214683211860390880917957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77476455474573593920611971 116214683211860390880917957)
                ·
                  refine ⟨21790253102223823290172117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116214683211860390880917957 21790253102223823290172117)
                  ·
                    refine ⟨510709057083370858363409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21790253102223823290172117 510709057083370858363409)
                    ·
                      rfl

theorem cell23_2983807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 7].length) (baseStart_2983807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983807 prefixEnd_2983807 := by exact prefixLift 2983807
  have htrace : WordTrace (prefixWord ++ tailWord_2983807) baseStart_2983807 baseEnd_2983807 := by
    simpa [prefixWord, tailWord_2983807, baseEnd_2983807] using wordTrace_append hprefix tailTrace_2983807
  have hstable : (prefixWord ++ tailWord_2983807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983807).length < 2 ^ (prefixWord ++ tailWord_2983807).sum := by decide
  have hdescent : baseEnd_2983807 < baseStart_2983807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983822 : List Nat := [4, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4]
def baseStart_2983822 : Nat := 118140960795 + 2983822 * 2 ^ 59
def prefixEnd_2983822 : Nat := 4983230072969 + 3 ^ 40 * 2983822 * 2
def baseEnd_2983822 : Nat := 1532134873459930016402659

theorem tailTrace_2983822 : CollatzResearch.WordTrace tailWord_2983822 prefixEnd_2983822 1532134873459930016402659 := by
  unfold tailWord_2983822
  simp only [CollatzResearch.WordTrace]
  refine ⟨13603616124516245633960215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72552619330753310047787813 13603616124516245633960215)
  ·
    refine ⟨20405424186774368450940323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13603616124516245633960215 20405424186774368450940323)
    ·
      refine ⟨30608136280161552676410485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20405424186774368450940323 30608136280161552676410485)
      ·
        refine ⟨2869512776265145563413483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30608136280161552676410485 2869512776265145563413483)
        ·
          refine ⟨4304269164397718345120225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2869512776265145563413483 4304269164397718345120225)
          ·
            refine ⟨3228201873298288758840169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4304269164397718345120225 3228201873298288758840169)
            ·
              refine ⟨2421151404973716569130127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3228201873298288758840169 2421151404973716569130127)
              ·
                refine ⟨3631727107460574853695191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2421151404973716569130127 3631727107460574853695191)
                ·
                  refine ⟨5447590661190862280542787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3631727107460574853695191 5447590661190862280542787)
                  ·
                    refine ⟨8171385991786293420814181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5447590661190862280542787 8171385991786293420814181)
                    ·
                      refine ⟨1532134873459930016402659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8171385991786293420814181 1532134873459930016402659)
                      ·
                        rfl

theorem cell23_2983822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_2983822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983822 prefixEnd_2983822 := by exact prefixLift 2983822
  have htrace : WordTrace (prefixWord ++ tailWord_2983822) baseStart_2983822 baseEnd_2983822 := by
    simpa [prefixWord, tailWord_2983822, baseEnd_2983822] using wordTrace_append hprefix tailTrace_2983822
  have hstable : (prefixWord ++ tailWord_2983822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983822).length < 2 ^ (prefixWord ++ tailWord_2983822).sum := by decide
  have hdescent : baseEnd_2983822 < baseStart_2983822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983832 : List Nat := [2, 1, 2, 6, 2, 1, 1, 2, 2, 4]
def baseStart_2983832 : Nat := 118140960795 + 2983832 * 2 ^ 59
def prefixEnd_2983832 : Nat := 4983230072969 + 3 ^ 40 * 2983832 * 2
def baseEnd_2983832 : Nat := 510713336088824992425871

theorem tailTrace_2983832 : CollatzResearch.WordTrace tailWord_2983832 prefixEnd_2983832 510713336088824992425871 := by
  unfold tailWord_2983832
  simp only [CollatzResearch.WordTrace]
  refine ⟨54414646863046868389772875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72552862484062491186363833 54414646863046868389772875)
  ·
    refine ⟨81621970294570302584659313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54414646863046868389772875 81621970294570302584659313)
    ·
      refine ⟨61216477720927726938494485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81621970294570302584659313 61216477720927726938494485)
      ·
        refine ⟨2869522393168487200241929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61216477720927726938494485 2869522393168487200241929)
        ·
          refine ⟨2152141794876365400181447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2869522393168487200241929 2152141794876365400181447)
          ·
            refine ⟨3228212692314548100272171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152141794876365400181447 3228212692314548100272171)
            ·
              refine ⟨4842319038471822150408257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228212692314548100272171 4842319038471822150408257)
              ·
                refine ⟨3631739278853866612806193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4842319038471822150408257 3631739278853866612806193)
                ·
                  refine ⟨2723804459140399959604645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3631739278853866612806193 2723804459140399959604645)
                  ·
                    refine ⟨510713336088824992425871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2723804459140399959604645 510713336088824992425871)
                    ·
                      rfl

theorem cell23_2983832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 2, 4].length) (baseStart_2983832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983832 prefixEnd_2983832 := by exact prefixLift 2983832
  have htrace : WordTrace (prefixWord ++ tailWord_2983832) baseStart_2983832 baseEnd_2983832 := by
    simpa [prefixWord, tailWord_2983832, baseEnd_2983832] using wordTrace_append hprefix tailTrace_2983832
  have hstable : (prefixWord ++ tailWord_2983832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983832).length < 2 ^ (prefixWord ++ tailWord_2983832).sum := by decide
  have hdescent : baseEnd_2983832 < baseStart_2983832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983864 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 2, 1, 5]
def baseStart_2983864 : Nat := 118140960795 + 2983864 * 2 ^ 59
def prefixEnd_2983864 : Nat := 4983230072969 + 3 ^ 40 * 2983864 * 2
def baseEnd_2983864 : Nat := 1532156439647418852077465

theorem tailTrace_2983864 : CollatzResearch.WordTrace tailWord_2983864 prefixEnd_2983864 1532156439647418852077465 := by
  unfold tailWord_2983864
  simp only [CollatzResearch.WordTrace]
  refine ⟨54415230430988903122355323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72553640574651870829807097 54415230430988903122355323)
  ·
    refine ⟨81622845646483354683532985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54415230430988903122355323 81622845646483354683532985)
    ·
      refine ⟨61217134234862516012649739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81622845646483354683532985 61217134234862516012649739)
      ·
        refine ⟨91825701352293774018974609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61217134234862516012649739 91825701352293774018974609)
        ·
          refine ⟨68869276014220330514230957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91825701352293774018974609 68869276014220330514230957)
          ·
            refine ⟨25825978505332623942836609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68869276014220330514230957 25825978505332623942836609)
            ·
              refine ⟨19369483878999467957127457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25825978505332623942836609 19369483878999467957127457)
              ·
                refine ⟨14527112909249600967845593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19369483878999467957127457 14527112909249600967845593)
                ·
                  refine ⟨10895334681937200725884195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14527112909249600967845593 10895334681937200725884195)
                  ·
                    refine ⟨16343002022905801088826293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10895334681937200725884195 16343002022905801088826293)
                    ·
                      refine ⟨1532156439647418852077465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16343002022905801088826293 1532156439647418852077465)
                      ·
                        rfl

theorem cell23_2983864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_2983864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983864 prefixEnd_2983864 := by exact prefixLift 2983864
  have htrace : WordTrace (prefixWord ++ tailWord_2983864) baseStart_2983864 baseEnd_2983864 := by
    simpa [prefixWord, tailWord_2983864, baseEnd_2983864] using wordTrace_append hprefix tailTrace_2983864
  have hstable : (prefixWord ++ tailWord_2983864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983864).length < 2 ^ (prefixWord ++ tailWord_2983864).sum := by decide
  have hdescent : baseEnd_2983864 < baseStart_2983864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983906 : List Nat := [3, 3, 3, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_2983906 : Nat := 118140960795 + 2983906 * 2 ^ 59
def prefixEnd_2983906 : Nat := 4983230072969 + 3 ^ 40 * 2983906 * 2
def baseEnd_2983906 : Nat := 1532178005834907687752273

theorem tailTrace_2983906 : CollatzResearch.WordTrace tailWord_2983906 prefixEnd_2983906 1532178005834907687752273 := by
  unfold tailWord_2983906
  simp only [CollatzResearch.WordTrace]
  refine ⟨27207998181956411854434893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72554661818550431611826381 27207998181956411854434893)
  ·
    refine ⟨10202999318233654445413085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27207998181956411854434893 10202999318233654445413085)
    ·
      refine ⟨3826124744337620417029907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10202999318233654445413085 3826124744337620417029907)
      ·
        refine ⟨5739187116506430625544861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3826124744337620417029907 5739187116506430625544861)
        ·
          refine ⟨2152195168689911484579323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5739187116506430625544861 2152195168689911484579323)
          ·
            refine ⟨3228292753034867226868985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152195168689911484579323 3228292753034867226868985)
            ·
              refine ⟨2421219564776150420151739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3228292753034867226868985 2421219564776150420151739)
              ·
                refine ⟨3631829347164225630227609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2421219564776150420151739 3631829347164225630227609)
                ·
                  refine ⟨2723872010373169222670707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3631829347164225630227609 2723872010373169222670707)
                  ·
                    refine ⟨4085808015559753834006061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2723872010373169222670707 4085808015559753834006061)
                    ·
                      refine ⟨1532178005834907687752273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4085808015559753834006061 1532178005834907687752273)
                      ·
                        rfl

theorem cell23_2983906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_2983906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983906 prefixEnd_2983906 := by exact prefixLift 2983906
  have htrace : WordTrace (prefixWord ++ tailWord_2983906) baseStart_2983906 baseEnd_2983906 := by
    simpa [prefixWord, tailWord_2983906, baseEnd_2983906] using wordTrace_append hprefix tailTrace_2983906
  have hstable : (prefixWord ++ tailWord_2983906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983906).length < 2 ^ (prefixWord ++ tailWord_2983906).sum := by decide
  have hdescent : baseEnd_2983906 < baseStart_2983906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983961 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 3, 4]
def baseStart_2983961 : Nat := 118140960795 + 2983961 * 2 ^ 59
def prefixEnd_2983961 : Nat := 4983230072969 + 3 ^ 40 * 2983961 * 2
def baseEnd_2983961 : Nat := 510735415756968324188173

theorem tailTrace_2983961 : CollatzResearch.WordTrace tailWord_2983961 prefixEnd_2983961 510735415756968324188173 := by
  unfold tailWord_2983961
  simp only [CollatzResearch.WordTrace]
  refine ⟨108833998742626391810991737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72555999161750927873994491 108833998742626391810991737)
  ·
    refine ⟨81625499056969793858243803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108833998742626391810991737 81625499056969793858243803)
    ·
      refine ⟨122438248585454690787365705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81625499056969793858243803 122438248585454690787365705)
      ·
        refine ⟨91828686439091018090524279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122438248585454690787365705 91828686439091018090524279)
        ·
          refine ⟨137743029658636527135786419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91828686439091018090524279 137743029658636527135786419)
          ·
            refine ⟨206614544487954790703679629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137743029658636527135786419 206614544487954790703679629)
            ·
              refine ⟨77480454182983046513879861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206614544487954790703679629 77480454182983046513879861)
              ·
                refine ⟨7263792579654660610676237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77480454182983046513879861 7263792579654660610676237)
                ·
                  refine ⟨2723922217370497729003589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7263792579654660610676237 2723922217370497729003589)
                  ·
                    refine ⟨510735415756968324188173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2723922217370497729003589 510735415756968324188173)
                    ·
                      rfl

theorem cell23_2983961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 4].length) (baseStart_2983961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983961 prefixEnd_2983961 := by exact prefixLift 2983961
  have htrace : WordTrace (prefixWord ++ tailWord_2983961) baseStart_2983961 baseEnd_2983961 := by
    simpa [prefixWord, tailWord_2983961, baseEnd_2983961] using wordTrace_append hprefix tailTrace_2983961
  have hstable : (prefixWord ++ tailWord_2983961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983961).length < 2 ^ (prefixWord ++ tailWord_2983961).sum := by decide
  have hdescent : baseEnd_2983961 < baseStart_2983961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983971 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 3]
def baseStart_2983971 : Nat := 118140960795 + 2983971 * 2 ^ 59
def prefixEnd_2983971 : Nat := 4983230072969 + 3 ^ 40 * 2983971 * 2
def baseEnd_2983971 : Nat := 1532211382077449933439473

theorem tailTrace_2983971 : CollatzResearch.WordTrace tailWord_2983971 prefixEnd_2983971 1532211382077449933439473 := by
  unfold tailWord_2983971
  simp only [CollatzResearch.WordTrace]
  refine ⟨108834363472590163518855767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72556242315060109012570511 108834363472590163518855767)
  ·
    refine ⟨163251545208885245278283651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108834363472590163518855767 163251545208885245278283651)
    ·
      refine ⟨244877317813327867917425477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163251545208885245278283651 244877317813327867917425477)
      ·
        refine ⟨45914497089998975234517277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244877317813327867917425477 45914497089998975234517277)
        ·
          refine ⟨17217936408749615712943979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45914497089998975234517277 17217936408749615712943979)
          ·
            refine ⟨25826904613124423569415969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17217936408749615712943979 25826904613124423569415969)
            ·
              refine ⟨19370178459843317677061977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25826904613124423569415969 19370178459843317677061977)
              ·
                refine ⟨14527633844882488257796483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19370178459843317677061977 14527633844882488257796483)
                ·
                  refine ⟨21791450767323732386694725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14527633844882488257796483 21791450767323732386694725)
                  ·
                    refine ⟨4085897018873199822505261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21791450767323732386694725 4085897018873199822505261)
                    ·
                      refine ⟨1532211382077449933439473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4085897018873199822505261 1532211382077449933439473)
                      ·
                        rfl

theorem cell23_2983971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_2983971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983971 prefixEnd_2983971 := by exact prefixLift 2983971
  have htrace : WordTrace (prefixWord ++ tailWord_2983971) baseStart_2983971 baseEnd_2983971 := by
    simpa [prefixWord, tailWord_2983971, baseEnd_2983971] using wordTrace_append hprefix tailTrace_2983971
  have hstable : (prefixWord ++ tailWord_2983971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983971).length < 2 ^ (prefixWord ++ tailWord_2983971).sum := by decide
  have hdescent : baseEnd_2983971 < baseStart_2983971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2983978 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 5, 4]
def baseStart_2983978 : Nat := 118140960795 + 2983978 * 2 ^ 59
def prefixEnd_2983978 : Nat := 4983230072969 + 3 ^ 40 * 2983978 * 2
def baseEnd_2983978 : Nat := 510738325480677135350647

theorem tailTrace_2983978 : CollatzResearch.WordTrace tailWord_2983978 prefixEnd_2983978 510738325480677135350647 := by
  unfold tailWord_2983978
  simp only [CollatzResearch.WordTrace]
  refine ⟨27208654695891200928590147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72556412522376535809573725 27208654695891200928590147)
  ·
    refine ⟨40812982043836801392885221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27208654695891200928590147 40812982043836801392885221)
    ·
      refine ⟨7652434133219400261165979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40812982043836801392885221 7652434133219400261165979)
      ·
        refine ⟨11478651199829100391748969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7652434133219400261165979 11478651199829100391748969)
        ·
          refine ⟨8608988399871825293811727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11478651199829100391748969 8608988399871825293811727)
          ·
            refine ⟨12913482599807737940717591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8608988399871825293811727 12913482599807737940717591)
            ·
              refine ⟨19370223899711606911076387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12913482599807737940717591 19370223899711606911076387)
              ·
                refine ⟨29055335849567410366614581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19370223899711606911076387 29055335849567410366614581)
                ·
                  refine ⟨2723937735896944721870117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29055335849567410366614581 2723937735896944721870117)
                  ·
                    refine ⟨510738325480677135350647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2723937735896944721870117 510738325480677135350647)
                    ·
                      rfl

theorem cell23_2983978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_2983978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2983978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2983978 prefixEnd_2983978 := by exact prefixLift 2983978
  have htrace : WordTrace (prefixWord ++ tailWord_2983978) baseStart_2983978 baseEnd_2983978 := by
    simpa [prefixWord, tailWord_2983978, baseEnd_2983978] using wordTrace_append hprefix tailTrace_2983978
  have hstable : (prefixWord ++ tailWord_2983978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2983978).length < 2 ^ (prefixWord ++ tailWord_2983978).sum := by decide
  have hdescent : baseEnd_2983978 < baseStart_2983978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2983978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984045 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 2, 3, 2]
def baseStart_2984045 : Nat := 118140960795 + 2984045 * 2 ^ 59
def prefixEnd_2984045 : Nat := 4983230072969 + 3 ^ 40 * 2984045 * 2
def baseEnd_2984045 : Nat := 1532249379645882643914133

theorem tailTrace_2984045 : CollatzResearch.WordTrace tailWord_2984045 prefixEnd_2984045 1532249379645882643914133 := by
  unfold tailWord_2984045
  simp only [CollatzResearch.WordTrace]
  refine ⟨108837062474322074157049589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72558041649548049438033059 108837062474322074157049589)
  ·
    refine ⟨10203474606967694452223399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108837062474322074157049589 10203474606967694452223399)
    ·
      refine ⟨15305211910451541678335099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10203474606967694452223399 15305211910451541678335099)
      ·
        refine ⟨22957817865677312517502649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15305211910451541678335099 22957817865677312517502649)
        ·
          refine ⟨17218363399257984388126987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22957817865677312517502649 17218363399257984388126987)
          ·
            refine ⟨25827545098886976582190481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17218363399257984388126987 25827545098886976582190481)
            ·
              refine ⟨19370658824165232436642861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25827545098886976582190481 19370658824165232436642861)
              ·
                refine ⟨7263997059061962163741073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19370658824165232436642861 7263997059061962163741073)
                ·
                  refine ⟨5447997794296471622805805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7263997059061962163741073 5447997794296471622805805)
                  ·
                    refine ⟨2042999172861176858552177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5447997794296471622805805 2042999172861176858552177)
                    ·
                      refine ⟨1532249379645882643914133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2042999172861176858552177 1532249379645882643914133)
                      ·
                        rfl

theorem cell23_2984045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_2984045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984045 prefixEnd_2984045 := by exact prefixLift 2984045
  have htrace : WordTrace (prefixWord ++ tailWord_2984045) baseStart_2984045 baseEnd_2984045 := by
    simpa [prefixWord, tailWord_2984045, baseEnd_2984045] using wordTrace_append hprefix tailTrace_2984045
  have hstable : (prefixWord ++ tailWord_2984045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984045).length < 2 ^ (prefixWord ++ tailWord_2984045).sum := by decide
  have hdescent : baseEnd_2984045 < baseStart_2984045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984068 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 4, 4]
def baseStart_2984068 : Nat := 118140960795 + 2984068 * 2 ^ 59
def prefixEnd_2984068 : Nat := 4983230072969 + 3 ^ 40 * 2984068 * 2
def baseEnd_2984068 : Nat := 510753729900312017975509

theorem tailTrace_2984068 : CollatzResearch.WordTrace tailWord_2984068 prefixEnd_2984068 510753729900312017975509 := by
  unfold tailWord_2984068
  simp only [CollatzResearch.WordTrace]
  refine ⟨54418950676619374542568429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72558600902159166056757905 54418950676619374542568429)
  ·
    refine ⟨20407106503732265453463161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54418950676619374542568429 20407106503732265453463161)
    ·
      refine ⟨15305329877799199090097371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20407106503732265453463161 15305329877799199090097371)
      ·
        refine ⟨22957994816698798635146057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15305329877799199090097371 22957994816698798635146057)
        ·
          refine ⟨17218496112524098976359543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22957994816698798635146057 17218496112524098976359543)
          ·
            refine ⟨25827744168786148464539315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17218496112524098976359543 25827744168786148464539315)
            ·
              refine ⟨38741616253179222696808973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25827744168786148464539315 38741616253179222696808973)
              ·
                refine ⟨14528106094942208511303365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38741616253179222696808973 14528106094942208511303365)
                ·
                  refine ⟨2724019892801664095869381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14528106094942208511303365 2724019892801664095869381)
                  ·
                    refine ⟨510753729900312017975509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2724019892801664095869381 510753729900312017975509)
                    ·
                      rfl

theorem cell23_2984068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_2984068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984068 prefixEnd_2984068 := by exact prefixLift 2984068
  have htrace : WordTrace (prefixWord ++ tailWord_2984068) baseStart_2984068 baseEnd_2984068 := by
    simpa [prefixWord, tailWord_2984068, baseEnd_2984068] using wordTrace_append hprefix tailTrace_2984068
  have hstable : (prefixWord ++ tailWord_2984068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984068).length < 2 ^ (prefixWord ++ tailWord_2984068).sum := by decide
  have hdescent : baseEnd_2984068 < baseStart_2984068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984069 : List Nat := [1, 3, 1, 1, 5, 2, 3, 2, 1, 1, 3]
def baseStart_2984069 : Nat := 118140960795 + 2984069 * 2 ^ 59
def prefixEnd_2984069 : Nat := 4983230072969 + 3 ^ 40 * 2984069 * 2
def baseEnd_2984069 : Nat := 1532261703181590550014023

theorem tailTrace_2984069 : CollatzResearch.WordTrace tailWord_2984069 prefixEnd_2984069 1532261703181590550014023 := by
  unfold tailWord_2984069
  simp only [CollatzResearch.WordTrace]
  refine ⟨108837937826235126255923261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72558625217490084170615507 108837937826235126255923261)
  ·
    refine ⟨40814226684838172345971223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108837937826235126255923261 40814226684838172345971223)
    ·
      refine ⟨61221340027257258518956835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40814226684838172345971223 61221340027257258518956835)
      ·
        refine ⟨91832010040885887778435253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61221340027257258518956835 91832010040885887778435253)
        ·
          refine ⟨8609250941333051979228305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91832010040885887778435253 8609250941333051979228305)
          ·
            refine ⟨6456938205999788984421229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8609250941333051979228305 6456938205999788984421229)
            ·
              refine ⟨2421351827249920869157961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6456938205999788984421229 2421351827249920869157961)
              ·
                refine ⟨1816013870437440651868471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2421351827249920869157961 1816013870437440651868471)
                ·
                  refine ⟨2724020805656160977802707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816013870437440651868471 2724020805656160977802707)
                  ·
                    refine ⟨4086031208484241466704061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2724020805656160977802707 4086031208484241466704061)
                    ·
                      refine ⟨1532261703181590550014023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4086031208484241466704061 1532261703181590550014023)
                      ·
                        rfl

theorem cell23_2984069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 1, 1, 3].length) (baseStart_2984069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984069 prefixEnd_2984069 := by exact prefixLift 2984069
  have htrace : WordTrace (prefixWord ++ tailWord_2984069) baseStart_2984069 baseEnd_2984069 := by
    simpa [prefixWord, tailWord_2984069, baseEnd_2984069] using wordTrace_append hprefix tailTrace_2984069
  have hstable : (prefixWord ++ tailWord_2984069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984069).length < 2 ^ (prefixWord ++ tailWord_2984069).sum := by decide
  have hdescent : baseEnd_2984069 < baseStart_2984069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984071 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_2984071 : Nat := 118140960795 + 2984071 * 2 ^ 59
def prefixEnd_2984071 : Nat := 4983230072969 + 3 ^ 40 * 2984071 * 2
def baseEnd_2984071 : Nat := 1532262730142899542189013

theorem tailTrace_2984071 : CollatzResearch.WordTrace tailWord_2984071 prefixEnd_2984071 1532262730142899542189013 := by
  unfold tailWord_2984071
  simp only [CollatzResearch.WordTrace]
  refine ⟨108838010772227880597496067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72558673848151920398330711 108838010772227880597496067)
  ·
    refine ⟨163257016158341820896244101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108838010772227880597496067 163257016158341820896244101)
    ·
      refine ⟨30610690529689091418045769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163257016158341820896244101 30610690529689091418045769)
      ·
        refine ⟨22958017897266818563534327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30610690529689091418045769 22958017897266818563534327)
        ·
          refine ⟨34437026845900227845301491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22958017897266818563534327 34437026845900227845301491)
          ·
            refine ⟨51655540268850341767952237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34437026845900227845301491 51655540268850341767952237)
            ·
              refine ⟨19370827600818878162982089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51655540268850341767952237 19370827600818878162982089)
              ·
                refine ⟨14528120700614158622236567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19370827600818878162982089 14528120700614158622236567)
                ·
                  refine ⟨21792181050921237933354851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14528120700614158622236567 21792181050921237933354851)
                  ·
                    refine ⟨32688271576381856900032277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21792181050921237933354851 32688271576381856900032277)
                    ·
                      refine ⟨1532262730142899542189013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32688271576381856900032277 1532262730142899542189013)
                      ·
                        rfl

theorem cell23_2984071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_2984071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984071 prefixEnd_2984071 := by exact prefixLift 2984071
  have htrace : WordTrace (prefixWord ++ tailWord_2984071) baseStart_2984071 baseEnd_2984071 := by
    simpa [prefixWord, tailWord_2984071, baseEnd_2984071] using wordTrace_append hprefix tailTrace_2984071
  have hstable : (prefixWord ++ tailWord_2984071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984071).length < 2 ^ (prefixWord ++ tailWord_2984071).sum := by decide
  have hdescent : baseEnd_2984071 < baseStart_2984071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984095 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 3]
def baseStart_2984095 : Nat := 118140960795 + 2984095 * 2 ^ 59
def prefixEnd_2984095 : Nat := 4983230072969 + 3 ^ 40 * 2984095 * 2
def baseEnd_2984095 : Nat := 1532275053678607448288903

theorem tailTrace_2984095 : CollatzResearch.WordTrace tailWord_2984095 prefixEnd_2984095 1532275053678607448288903 := by
  unfold tailWord_2984095
  simp only [CollatzResearch.WordTrace]
  refine ⟨108838886124140932696369739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72559257416093955130913159 108838886124140932696369739)
  ·
    refine ⟨163258329186211399044554609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108838886124140932696369739 163258329186211399044554609)
    ·
      refine ⟨122443746889658549283415957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163258329186211399044554609 122443746889658549283415957)
      ·
        refine ⟨5739550635452744497660123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122443746889658549283415957 5739550635452744497660123)
        ·
          refine ⟨8609325953179116746490185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5739550635452744497660123 8609325953179116746490185)
          ·
            refine ⟨6456994464884337559867639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8609325953179116746490185 6456994464884337559867639)
            ·
              refine ⟨9685491697326506339801459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6456994464884337559867639 9685491697326506339801459)
              ·
                refine ⟨14528237545989759509702189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9685491697326506339801459 14528237545989759509702189)
                ·
                  refine ⟨5448089079746159816138321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14528237545989759509702189 5448089079746159816138321)
                  ·
                    refine ⟨4086066809809619862103741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5448089079746159816138321 4086066809809619862103741)
                    ·
                      refine ⟨1532275053678607448288903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4086066809809619862103741 1532275053678607448288903)
                      ·
                        rfl

theorem cell23_2984095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_2984095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984095 prefixEnd_2984095 := by exact prefixLift 2984095
  have htrace : WordTrace (prefixWord ++ tailWord_2984095) baseStart_2984095 baseEnd_2984095 := by
    simpa [prefixWord, tailWord_2984095, baseEnd_2984095] using wordTrace_append hprefix tailTrace_2984095
  have hstable : (prefixWord ++ tailWord_2984095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984095).length < 2 ^ (prefixWord ++ tailWord_2984095).sum := by decide
  have hdescent : baseEnd_2984095 < baseStart_2984095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984098 : List Nat := [3, 3, 1, 3, 1, 1, 2, 9]
def baseStart_2984098 : Nat := 118140960795 + 2984098 * 2 ^ 59
def prefixEnd_2984098 : Nat := 4983230072969 + 3 ^ 40 * 2984098 * 2
def baseEnd_2984098 : Nat := 56750984967428553205607

theorem tailTrace_2984098 : CollatzResearch.WordTrace tailWord_2984098 prefixEnd_2984098 56750984967428553205607 := by
  unfold tailWord_2984098
  simp only [CollatzResearch.WordTrace]
  refine ⟨27209748885782516052182237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72559330362086709472485965 27209748885782516052182237)
  ·
    refine ⟨10203655832168443519568339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27209748885782516052182237 10203655832168443519568339)
    ·
      refine ⟨15305483748252665279352509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10203655832168443519568339 15305483748252665279352509)
      ·
        refine ⟨5739556405594749479757191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15305483748252665279352509 5739556405594749479757191)
        ·
          refine ⟨8609334608392124219635787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5739556405594749479757191 8609334608392124219635787)
          ·
            refine ⟨12914001912588186329453681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8609334608392124219635787 12914001912588186329453681)
            ·
              refine ⟨9685501434441139747090261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12914001912588186329453681 9685501434441139747090261)
              ·
                refine ⟨56750984967428553205607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9685501434441139747090261 56750984967428553205607)
                ·
                  rfl

theorem cell23_2984098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 9].length) (baseStart_2984098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984098 prefixEnd_2984098 := by exact prefixLift 2984098
  have htrace : WordTrace (prefixWord ++ tailWord_2984098) baseStart_2984098 baseEnd_2984098 := by
    simpa [prefixWord, tailWord_2984098, baseEnd_2984098] using wordTrace_append hprefix tailTrace_2984098
  have hstable : (prefixWord ++ tailWord_2984098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984098).length < 2 ^ (prefixWord ++ tailWord_2984098).sum := by decide
  have hdescent : baseEnd_2984098 < baseStart_2984098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984126 : List Nat := [4, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2]
def baseStart_2984126 : Nat := 118140960795 + 2984126 * 2 ^ 59
def prefixEnd_2984126 : Nat := 4983230072969 + 3 ^ 40 * 2984126 * 2
def baseEnd_2984126 : Nat := 1532290971578896827001261

theorem tailTrace_2984126 : CollatzResearch.WordTrace tailWord_2984126 prefixEnd_2984126 1532290971578896827001261 := by
  unfold tailWord_2984126
  simp only [CollatzResearch.WordTrace]
  refine ⟨13605002098378578123843529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72560011191352416660498821 13605002098378578123843529)
  ·
    refine ⟨10203751573783933592882647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13605002098378578123843529 10203751573783933592882647)
    ·
      refine ⟨15305627360675900389323971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10203751573783933592882647 15305627360675900389323971)
      ·
        refine ⟨22958441041013850583985957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15305627360675900389323971 22958441041013850583985957)
        ·
          refine ⟨4304707695190096984497367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22958441041013850583985957 4304707695190096984497367)
          ·
            refine ⟨6457061542785145476746051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304707695190096984497367 6457061542785145476746051)
            ·
              refine ⟨9685592314177718215119077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6457061542785145476746051 9685592314177718215119077)
              ·
                refine ⟨1816048558908322165334827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9685592314177718215119077 1816048558908322165334827)
                ·
                  refine ⟨2724072838362483248002241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816048558908322165334827 2724072838362483248002241)
                  ·
                    refine ⟨2043054628771862436001681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2724072838362483248002241 2043054628771862436001681)
                    ·
                      refine ⟨1532290971578896827001261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2043054628771862436001681 1532290971578896827001261)
                      ·
                        rfl

theorem cell23_2984126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_2984126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984126 prefixEnd_2984126 := by exact prefixLift 2984126
  have htrace : WordTrace (prefixWord ++ tailWord_2984126) baseStart_2984126 baseEnd_2984126 := by
    simpa [prefixWord, tailWord_2984126, baseEnd_2984126] using wordTrace_append hprefix tailTrace_2984126
  have hstable : (prefixWord ++ tailWord_2984126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984126).length < 2 ^ (prefixWord ++ tailWord_2984126).sum := by decide
  have hdescent : baseEnd_2984126 < baseStart_2984126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984142 : List Nat := [4, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3]
def baseStart_2984142 : Nat := 118140960795 + 2984142 * 2 ^ 59
def prefixEnd_2984142 : Nat := 4983230072969 + 3 ^ 40 * 2984142 * 2
def baseEnd_2984142 : Nat := 1532299187269368764401187

theorem tailTrace_2984142 : CollatzResearch.WordTrace tailWord_2984142 prefixEnd_2984142 1532299187269368764401187 := by
  unfold tailWord_2984142
  simp only [CollatzResearch.WordTrace]
  refine ⟨13605075044371332465416335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72560400236647106482220453 13605075044371332465416335)
  ·
    refine ⟨20407612566556998698124503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13605075044371332465416335 20407612566556998698124503)
    ·
      refine ⟨30611418849835498047186755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20407612566556998698124503 30611418849835498047186755)
      ·
        refine ⟨45917128274753247070780133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30611418849835498047186755 45917128274753247070780133)
        ·
          refine ⟨8609461551516233825771275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45917128274753247070780133 8609461551516233825771275)
          ·
            refine ⟨12914192327274350738656913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8609461551516233825771275 12914192327274350738656913)
            ·
              refine ⟨9685644245455763053992685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12914192327274350738656913 9685644245455763053992685)
              ·
                refine ⟨3632116592045911145247257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9685644245455763053992685 3632116592045911145247257)
                ·
                  refine ⟨2724087444034433358935443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3632116592045911145247257 2724087444034433358935443)
                  ·
                    refine ⟨4086131166051650038403165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2724087444034433358935443 4086131166051650038403165)
                    ·
                      refine ⟨1532299187269368764401187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4086131166051650038403165 1532299187269368764401187)
                      ·
                        rfl

theorem cell23_2984142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_2984142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984142 prefixEnd_2984142 := by exact prefixLift 2984142
  have htrace : WordTrace (prefixWord ++ tailWord_2984142) baseStart_2984142 baseEnd_2984142 := by
    simpa [prefixWord, tailWord_2984142, baseEnd_2984142] using wordTrace_append hprefix tailTrace_2984142
  have hstable : (prefixWord ++ tailWord_2984142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984142).length < 2 ^ (prefixWord ++ tailWord_2984142).sum := by decide
  have hdescent : baseEnd_2984142 < baseStart_2984142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984171 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 9]
def baseStart_2984171 : Nat := 118140960795 + 2984171 * 2 ^ 59
def prefixEnd_2984171 : Nat := 4983230072969 + 3 ^ 40 * 2984171 * 2
def baseEnd_2984171 : Nat := 170257119800927683437617

theorem tailTrace_2984171 : CollatzResearch.WordTrace tailWord_2984171 prefixEnd_2984171 170257119800927683437617 := by
  unfold tailWord_2984171
  simp only [CollatzResearch.WordTrace]
  refine ⟨108841658071865597676136367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72561105381243731784090911 108841658071865597676136367)
  ·
    refine ⟨163262487107798396514204551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108841658071865597676136367 163262487107798396514204551)
    ·
      refine ⟨244893730661697594771306827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163262487107798396514204551 244893730661697594771306827)
      ·
        refine ⟨367340595992546392156960241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244893730661697594771306827 367340595992546392156960241)
        ·
          refine ⟨275505446994409794117720181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367340595992546392156960241 275505446994409794117720181)
          ·
            refine ⟨25828635655725918198536267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 275505446994409794117720181 25828635655725918198536267)
            ·
              refine ⟨38742953483588877297804401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25828635655725918198536267 38742953483588877297804401)
              ·
                refine ⟨29057215112691657973353301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38742953483588877297804401 29057215112691657973353301)
                ·
                  refine ⟨170257119800927683437617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29057215112691657973353301 170257119800927683437617)
                  ·
                    rfl

theorem cell23_2984171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 9].length) (baseStart_2984171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984171 prefixEnd_2984171 := by exact prefixLift 2984171
  have htrace : WordTrace (prefixWord ++ tailWord_2984171) baseStart_2984171 baseEnd_2984171 := by
    simpa [prefixWord, tailWord_2984171, baseEnd_2984171] using wordTrace_append hprefix tailTrace_2984171
  have hstable : (prefixWord ++ tailWord_2984171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984171).length < 2 ^ (prefixWord ++ tailWord_2984171).sum := by decide
  have hdescent : baseEnd_2984171 < baseStart_2984171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984188 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 7]
def baseStart_2984188 : Nat := 118140960795 + 2984188 * 2 ^ 59
def prefixEnd_2984188 : Nat := 4983230072969 + 3 ^ 40 * 2984188 * 2
def baseEnd_2984188 : Nat := 170258089708830620491775

theorem tailTrace_2984188 : CollatzResearch.WordTrace tailWord_2984188 prefixEnd_2984188 170258089708830620491775 := by
  unfold tailWord_2984188
  simp only [CollatzResearch.WordTrace]
  refine ⟨54421139056402004789752609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72561518741869339719670145 54421139056402004789752609)
  ·
    refine ⟨40815854292301503592314457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54421139056402004789752609 40815854292301503592314457)
    ·
      refine ⟨30611890719226127694235843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40815854292301503592314457 30611890719226127694235843)
      ·
        refine ⟨45917836078839191541353765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30611890719226127694235843 45917836078839191541353765)
        ·
          refine ⟨8609594264782348414003831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45917836078839191541353765 8609594264782348414003831)
          ·
            refine ⟨12914391397173522621005747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8609594264782348414003831 12914391397173522621005747)
            ·
              refine ⟨19371587095760283931508621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12914391397173522621005747 19371587095760283931508621)
              ·
                refine ⟨7264345160910106474315733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19371587095760283931508621 7264345160910106474315733)
                ·
                  refine ⟨170258089708830620491775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7264345160910106474315733 170258089708830620491775)
                  ·
                    rfl

theorem cell23_2984188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 7].length) (baseStart_2984188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984188 prefixEnd_2984188 := by exact prefixLift 2984188
  have htrace : WordTrace (prefixWord ++ tailWord_2984188) baseStart_2984188 baseEnd_2984188 := by
    simpa [prefixWord, tailWord_2984188, baseEnd_2984188] using wordTrace_append hprefix tailTrace_2984188
  have hstable : (prefixWord ++ tailWord_2984188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984188).length < 2 ^ (prefixWord ++ tailWord_2984188).sum := by decide
  have hdescent : baseEnd_2984188 < baseStart_2984188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984255 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 1, 6, 2]
def baseStart_2984255 : Nat := 118140960795 + 2984255 * 2 ^ 59
def prefixEnd_2984255 : Nat := 4983230072969 + 3 ^ 40 * 2984255 * 2
def baseEnd_2984255 : Nat := 1532357210583326822288167

theorem tailTrace_2984255 : CollatzResearch.WordTrace tailWord_2984255 prefixEnd_2984255 1532357210583326822288167 := by
  unfold tailWord_2984255
  simp only [CollatzResearch.WordTrace]
  refine ⟨108844721803561280022194219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72563147869040853348129479 108844721803561280022194219)
  ·
    refine ⟨163267082705341920033291329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108844721803561280022194219 163267082705341920033291329)
    ·
      refine ⟨122450312029006440024968497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163267082705341920033291329 122450312029006440024968497)
      ·
        refine ⟨91837734021754830018726373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122450312029006440024968497 91837734021754830018726373)
        ·
          refine ⟨17219575129079030628511195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91837734021754830018726373 17219575129079030628511195)
          ·
            refine ⟨25829362693618545942766793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17219575129079030628511195 25829362693618545942766793)
            ·
              refine ⟨19372022020213909457075095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25829362693618545942766793 19372022020213909457075095)
              ·
                refine ⟨29058033030320864185612643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19372022020213909457075095 29058033030320864185612643)
                ·
                  refine ⟨43587049545481296278418965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29058033030320864185612643 43587049545481296278418965)
                  ·
                    refine ⟨2043142947444435763050889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43587049545481296278418965 2043142947444435763050889)
                    ·
                      refine ⟨1532357210583326822288167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2043142947444435763050889 1532357210583326822288167)
                      ·
                        rfl

theorem cell23_2984255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 6, 2].length) (baseStart_2984255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984255 prefixEnd_2984255 := by exact prefixLift 2984255
  have htrace : WordTrace (prefixWord ++ tailWord_2984255) baseStart_2984255 baseEnd_2984255 := by
    simpa [prefixWord, tailWord_2984255, baseEnd_2984255] using wordTrace_append hprefix tailTrace_2984255
  have hstable : (prefixWord ++ tailWord_2984255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984255).length < 2 ^ (prefixWord ++ tailWord_2984255).sum := by decide
  have hdescent : baseEnd_2984255 < baseStart_2984255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984282 : List Nat := [3, 1, 1, 2, 1, 2, 1, 7, 1, 4]
def baseStart_2984282 : Nat := 118140960795 + 2984282 * 2 ^ 59
def prefixEnd_2984282 : Nat := 4983230072969 + 3 ^ 40 * 2984282 * 2
def baseEnd_2984282 : Nat := 510790358186999405550181

theorem tailTrace_2984282 : CollatzResearch.WordTrace tailWord_2984282 prefixEnd_2984282 510790358186999405550181 := by
  unfold tailWord_2984282
  simp only [CollatzResearch.WordTrace]
  refine ⟨27211426643615865908356775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72563804382975642422284733 27211426643615865908356775)
  ·
    refine ⟨40817139965423798862535163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27211426643615865908356775 40817139965423798862535163)
    ·
      refine ⟨61225709948135698293802745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40817139965423798862535163 61225709948135698293802745)
      ·
        refine ⟨45919282461101773720352059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61225709948135698293802745 45919282461101773720352059)
        ·
          refine ⟨68878923691652660580528089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45919282461101773720352059 68878923691652660580528089)
          ·
            refine ⟨51659192768739495435396067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68878923691652660580528089 51659192768739495435396067)
            ·
              refine ⟨77488789153109243153094101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51659192768739495435396067 77488789153109243153094101)
              ·
                refine ⟨1816143495775997886400643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 77488789153109243153094101 1816143495775997886400643)
                ·
                  refine ⟨2724215243663996829600965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816143495775997886400643 2724215243663996829600965)
                  ·
                    refine ⟨510790358186999405550181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2724215243663996829600965 510790358186999405550181)
                    ·
                      rfl

theorem cell23_2984282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 1, 4].length) (baseStart_2984282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984282 prefixEnd_2984282 := by exact prefixLift 2984282
  have htrace : WordTrace (prefixWord ++ tailWord_2984282) baseStart_2984282 baseEnd_2984282 := by
    simpa [prefixWord, tailWord_2984282, baseEnd_2984282] using wordTrace_append hprefix tailTrace_2984282
  have hstable : (prefixWord ++ tailWord_2984282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984282).length < 2 ^ (prefixWord ++ tailWord_2984282).sum := by decide
  have hdescent : baseEnd_2984282 < baseStart_2984282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984295 : List Nat := [1, 1, 5, 1, 3, 1, 1, 4, 6]
def baseStart_2984295 : Nat := 118140960795 + 2984295 * 2 ^ 59
def prefixEnd_2984295 : Nat := 4983230072969 + 3 ^ 40 * 2984295 * 2
def baseEnd_2984295 : Nat := 170264194423278518420887

theorem tailTrace_2984295 : CollatzResearch.WordTrace tailWord_2984295 prefixEnd_2984295 170264194423278518420887 := by
  unfold tailWord_2984295
  simp only [CollatzResearch.WordTrace]
  refine ⟨108846180723416366853650339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72564120482277577902433559 108846180723416366853650339)
  ·
    refine ⟨163269271085124550280475509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108846180723416366853650339 163269271085124550280475509)
    ·
      refine ⟨15306494164230426588794579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163269271085124550280475509 15306494164230426588794579)
      ·
        refine ⟨22959741246345639883191869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15306494164230426588794579 22959741246345639883191869)
        ·
          refine ⟨8609902967379614956196951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22959741246345639883191869 8609902967379614956196951)
          ·
            refine ⟨12914854451069422434295427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8609902967379614956196951 12914854451069422434295427)
            ·
              refine ⟨19372281676604133651443141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12914854451069422434295427 19372281676604133651443141)
              ·
                refine ⟨3632302814363275059645589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19372281676604133651443141 3632302814363275059645589)
                ·
                  refine ⟨170264194423278518420887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3632302814363275059645589 170264194423278518420887)
                  ·
                    rfl

theorem cell23_2984295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 6].length) (baseStart_2984295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984295 prefixEnd_2984295 := by exact prefixLift 2984295
  have htrace : WordTrace (prefixWord ++ tailWord_2984295) baseStart_2984295 baseEnd_2984295 := by
    simpa [prefixWord, tailWord_2984295, baseEnd_2984295] using wordTrace_append hprefix tailTrace_2984295
  have hstable : (prefixWord ++ tailWord_2984295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984295).length < 2 ^ (prefixWord ++ tailWord_2984295).sum := by decide
  have hdescent : baseEnd_2984295 < baseStart_2984295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984325 : List Nat := [1, 3, 1, 1, 3, 1, 1, 6, 1, 5]
def baseStart_2984325 : Nat := 118140960795 + 2984325 * 2 ^ 59
def prefixEnd_2984325 : Nat := 4983230072969 + 3 ^ 40 * 2984325 * 2
def baseEnd_2984325 : Nat := 510797718076380516137615

theorem tailTrace_2984325 : CollatzResearch.WordTrace tailWord_2984325 prefixEnd_2984325 510797718076380516137615 := by
  unfold tailWord_2984325
  simp only [CollatzResearch.WordTrace]
  refine ⟨108847274913307681977242429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72564849942205121318161619 108847274913307681977242429)
  ·
    refine ⟨40817728092490380741465911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108847274913307681977242429 40817728092490380741465911)
    ·
      refine ⟨61226592138735571112198867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40817728092490380741465911 61226592138735571112198867)
      ·
        refine ⟨91839888208103356668298301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61226592138735571112198867 91839888208103356668298301)
        ·
          refine ⟨34439958078038758750611863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91839888208103356668298301 34439958078038758750611863)
          ·
            refine ⟨51659937117058138125917795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34439958078038758750611863 51659937117058138125917795)
            ·
              refine ⟨77489905675587207188876693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51659937117058138125917795 77489905675587207188876693)
              ·
                refine ⟨3632339328543150336978595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77489905675587207188876693 3632339328543150336978595)
                ·
                  refine ⟨5448508992814725505467893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632339328543150336978595 5448508992814725505467893)
                  ·
                    refine ⟨510797718076380516137615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5448508992814725505467893 510797718076380516137615)
                    ·
                      rfl

theorem cell23_2984325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_2984325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984325 prefixEnd_2984325 := by exact prefixLift 2984325
  have htrace : WordTrace (prefixWord ++ tailWord_2984325) baseStart_2984325 baseEnd_2984325 := by
    simpa [prefixWord, tailWord_2984325, baseEnd_2984325] using wordTrace_append hprefix tailTrace_2984325
  have hstable : (prefixWord ++ tailWord_2984325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984325).length < 2 ^ (prefixWord ++ tailWord_2984325).sum := by decide
  have hdescent : baseEnd_2984325 < baseStart_2984325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984332 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 1, 5, 2]
def baseStart_2984332 : Nat := 118140960795 + 2984332 * 2 ^ 59
def prefixEnd_2984332 : Nat := 4983230072969 + 3 ^ 40 * 2984332 * 2
def baseEnd_2984332 : Nat := 1532396748593723021025313

theorem tailTrace_2984332 : CollatzResearch.WordTrace tailWord_2984332 prefixEnd_2984332 1532396748593723021025313 := by
  unfold tailWord_2984332
  simp only [CollatzResearch.WordTrace]
  refine ⟨54423765112141161086373625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72565020149521548115164833 54423765112141161086373625)
  ·
    refine ⟨40817823834105870814780219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54423765112141161086373625 40817823834105870814780219)
    ·
      refine ⟨61226735751158806222170329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40817823834105870814780219 61226735751158806222170329)
      ·
        refine ⟨45920051813369104666627747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61226735751158806222170329 45920051813369104666627747)
        ·
          refine ⟨68880077720053656999941621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45920051813369104666627747 68880077720053656999941621)
          ·
            refine ⟨6457507286255030343744527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68880077720053656999941621 6457507286255030343744527)
            ·
              refine ⟨9686260929382545515616791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6457507286255030343744527 9686260929382545515616791)
              ·
                refine ⟨14529391394073818273425187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9686260929382545515616791 14529391394073818273425187)
                ·
                  refine ⟨21794087091110727410137781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14529391394073818273425187 21794087091110727410137781)
                  ·
                    refine ⟨2043195664791630694700417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21794087091110727410137781 2043195664791630694700417)
                    ·
                      refine ⟨1532396748593723021025313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2043195664791630694700417 1532396748593723021025313)
                      ·
                        rfl

theorem cell23_2984332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_2984332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984332 prefixEnd_2984332 := by exact prefixLift 2984332
  have htrace : WordTrace (prefixWord ++ tailWord_2984332) baseStart_2984332 baseEnd_2984332 := by
    simpa [prefixWord, tailWord_2984332, baseEnd_2984332] using wordTrace_append hprefix tailTrace_2984332
  have hstable : (prefixWord ++ tailWord_2984332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984332).length < 2 ^ (prefixWord ++ tailWord_2984332).sum := by decide
  have hdescent : baseEnd_2984332 < baseStart_2984332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984375 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 6]
def baseStart_2984375 : Nat := 118140960795 + 2984375 * 2 ^ 59
def prefixEnd_2984375 : Nat := 4983230072969 + 3 ^ 40 * 2984375 * 2
def baseEnd_2984375 : Nat := 1532418828261866352787615

theorem tailTrace_2984375 : CollatzResearch.WordTrace tailWord_2984375 prefixEnd_2984375 1532418828261866352787615 := by
  unfold tailWord_2984375
  simp only [CollatzResearch.WordTrace]
  refine ⟨108849098563126540516562579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72566065708751027011041719 108849098563126540516562579)
  ·
    refine ⟨163273647844689810774843869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108849098563126540516562579 163273647844689810774843869)
    ·
      refine ⟨61227617941758679040566451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163273647844689810774843869 61227617941758679040566451)
      ·
        refine ⟨91841426912638018560849677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61227617941758679040566451 91841426912638018560849677)
        ·
          refine ⟨34440535092239256960318629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91841426912638018560849677 34440535092239256960318629)
          ·
            refine ⟨6457600329794860680059743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34440535092239256960318629 6457600329794860680059743)
            ·
              refine ⟨9686400494692291020089615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6457600329794860680059743 9686400494692291020089615)
              ·
                refine ⟨14529600742038436530134423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9686400494692291020089615 14529600742038436530134423)
                ·
                  refine ⟨21794401113057654795201635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14529600742038436530134423 21794401113057654795201635)
                  ·
                    refine ⟨32691601669586482192802453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21794401113057654795201635 32691601669586482192802453)
                    ·
                      refine ⟨1532418828261866352787615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32691601669586482192802453 1532418828261866352787615)
                      ·
                        rfl

theorem cell23_2984375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_2984375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984375 prefixEnd_2984375 := by exact prefixLift 2984375
  have htrace : WordTrace (prefixWord ++ tailWord_2984375) baseStart_2984375 baseEnd_2984375 := by
    simpa [prefixWord, tailWord_2984375, baseEnd_2984375] using wordTrace_append hprefix tailTrace_2984375
  have hstable : (prefixWord ++ tailWord_2984375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984375).length < 2 ^ (prefixWord ++ tailWord_2984375).sum := by decide
  have hdescent : baseEnd_2984375 < baseStart_2984375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984382 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_2984382 : Nat := 118140960795 + 2984382 * 2 ^ 59
def prefixEnd_2984382 : Nat := 4983230072969 + 3 ^ 40 * 2984382 * 2
def baseEnd_2984382 : Nat := 1532422422626447825400083

theorem tailTrace_2984382 : CollatzResearch.WordTrace tailWord_2984382 prefixEnd_2984382 1532422422626447825400083 := by
  unfold tailWord_2984382
  simp only [CollatzResearch.WordTrace]
  refine ⟨13606169234262647589008425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72566235916067453808044933 13606169234262647589008425)
  ·
    refine ⟨10204626925696985691756319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13606169234262647589008425 10204626925696985691756319)
    ·
      refine ⟨15306940388545478537634479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10204626925696985691756319 15306940388545478537634479)
      ·
        refine ⟨22960410582818217806451719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15306940388545478537634479 22960410582818217806451719)
        ·
          refine ⟨34440615874227326709677579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22960410582818217806451719 34440615874227326709677579)
          ·
            refine ⟨51660923811340990064516369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34440615874227326709677579 51660923811340990064516369)
            ·
              refine ⟨38745692858505742548387277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51660923811340990064516369 38745692858505742548387277)
              ·
                refine ⟨14529634821939653455645229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38745692858505742548387277 14529634821939653455645229)
                ·
                  refine ⟨5448613058227370045866961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14529634821939653455645229 5448613058227370045866961)
                  ·
                    refine ⟨4086459793670527534400221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5448613058227370045866961 4086459793670527534400221)
                    ·
                      refine ⟨1532422422626447825400083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4086459793670527534400221 1532422422626447825400083)
                      ·
                        rfl

theorem cell23_2984382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_2984382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984382 prefixEnd_2984382 := by exact prefixLift 2984382
  have htrace : WordTrace (prefixWord ++ tailWord_2984382) baseStart_2984382 baseEnd_2984382 := by
    simpa [prefixWord, tailWord_2984382, baseEnd_2984382] using wordTrace_append hprefix tailTrace_2984382
  have hstable : (prefixWord ++ tailWord_2984382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984382).length < 2 ^ (prefixWord ++ tailWord_2984382).sum := by decide
  have hdescent : baseEnd_2984382 < baseStart_2984382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984395 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 3]
def baseStart_2984395 : Nat := 118140960795 + 2984395 * 2 ^ 59
def prefixEnd_2984395 : Nat := 4983230072969 + 3 ^ 40 * 2984395 * 2
def baseEnd_2984395 : Nat := 1532429097874956274537523

theorem tailTrace_2984395 : CollatzResearch.WordTrace tailWord_2984395 prefixEnd_2984395 1532429097874956274537523 := by
  unfold tailWord_2984395
  simp only [CollatzResearch.WordTrace]
  refine ⟨108849828023054083932290639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72566552015369389288193759 108849828023054083932290639)
  ·
    refine ⟨163274742034581125898435959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108849828023054083932290639 163274742034581125898435959)
    ·
      refine ⟨244912113051871688847653939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163274742034581125898435959 244912113051871688847653939)
      ·
        refine ⟨367368169577807533271480909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244912113051871688847653939 367368169577807533271480909)
        ·
          refine ⟨137763063591677824976805341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367368169577807533271480909 137763063591677824976805341)
          ·
            refine ⟨51661148846879184366302003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137763063591677824976805341 51661148846879184366302003)
            ·
              refine ⟨77491723270318776549453005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51661148846879184366302003 77491723270318776549453005)
              ·
                refine ⟨29059396226369541206044877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77491723270318776549453005 29059396226369541206044877)
                ·
                  refine ⟨10897273584888577952266829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29059396226369541206044877 10897273584888577952266829)
                  ·
                    refine ⟨4086477594333216732100061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10897273584888577952266829 4086477594333216732100061)
                    ·
                      refine ⟨1532429097874956274537523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4086477594333216732100061 1532429097874956274537523)
                      ·
                        rfl

theorem cell23_2984395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 3].length) (baseStart_2984395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984395 prefixEnd_2984395 := by exact prefixLift 2984395
  have htrace : WordTrace (prefixWord ++ tailWord_2984395) baseStart_2984395 baseEnd_2984395 := by
    simpa [prefixWord, tailWord_2984395, baseEnd_2984395] using wordTrace_append hprefix tailTrace_2984395
  have hstable : (prefixWord ++ tailWord_2984395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984395).length < 2 ^ (prefixWord ++ tailWord_2984395).sum := by decide
  have hdescent : baseEnd_2984395 < baseStart_2984395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984472 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 2, 4, 3]
def baseStart_2984472 : Nat := 118140960795 + 2984472 * 2 ^ 59
def prefixEnd_2984472 : Nat := 4983230072969 + 3 ^ 40 * 2984472 * 2
def baseEnd_2984472 : Nat := 1532468635885352473274669

theorem tailTrace_2984472 : CollatzResearch.WordTrace tailWord_2984472 prefixEnd_2984472 1532468635885352473274669 := by
  unfold tailWord_2984472
  simp only [CollatzResearch.WordTrace]
  refine ⟨54426318221887563041421835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72568424295850084055229113 54426318221887563041421835)
  ·
    refine ⟨81639477332831344562132753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54426318221887563041421835 81639477332831344562132753)
    ·
      refine ⟨61229607999623508421599565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81639477332831344562132753 61229607999623508421599565)
      ·
        refine ⟨22961102999858815658099837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61229607999623508421599565 22961102999858815658099837)
        ·
          refine ⟨8610413624947055871787439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22961102999858815658099837 8610413624947055871787439)
          ·
            refine ⟨12915620437420583807681159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8610413624947055871787439 12915620437420583807681159)
            ·
              refine ⟨19373430656130875711521739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12915620437420583807681159 19373430656130875711521739)
              ·
                refine ⟨29060145984196313567282609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19373430656130875711521739 29060145984196313567282609)
                ·
                  refine ⟨21795109488147235175461957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29060145984196313567282609 21795109488147235175461957)
                  ·
                    refine ⟨4086583029027606595399117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21795109488147235175461957 4086583029027606595399117)
                    ·
                      refine ⟨1532468635885352473274669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4086583029027606595399117 1532468635885352473274669)
                      ·
                        rfl

theorem cell23_2984472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_2984472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984472 prefixEnd_2984472 := by exact prefixLift 2984472
  have htrace : WordTrace (prefixWord ++ tailWord_2984472) baseStart_2984472 baseEnd_2984472 := by
    simpa [prefixWord, tailWord_2984472, baseEnd_2984472] using wordTrace_append hprefix tailTrace_2984472
  have hstable : (prefixWord ++ tailWord_2984472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984472).length < 2 ^ (prefixWord ++ tailWord_2984472).sum := by decide
  have hdescent : baseEnd_2984472 < baseStart_2984472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984509 : List Nat := [1, 4, 1, 3, 2, 1, 1, 5, 5]
def baseStart_2984509 : Nat := 118140960795 + 2984509 * 2 ^ 59
def prefixEnd_2984509 : Nat := 4983230072969 + 3 ^ 40 * 2984509 * 2
def baseEnd_2984509 : Nat := 170276403852174314279111

theorem tailTrace_2984509 : CollatzResearch.WordTrace tailWord_2984509 prefixEnd_2984509 170276403852174314279111 := by
  unfold tailWord_2984509
  simp only [CollatzResearch.WordTrace]
  refine ⟨108853985944641081401940581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72569323963094054267960387 108853985944641081401940581)
  ·
    refine ⟨20410122364620202762863859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108853985944641081401940581 20410122364620202762863859)
    ·
      refine ⟨30615183546930304144295789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20410122364620202762863859 30615183546930304144295789)
      ·
        refine ⟨11480693830098864054110921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30615183546930304144295789 11480693830098864054110921)
        ·
          refine ⟨8610520372574148040583191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11480693830098864054110921 8610520372574148040583191)
          ·
            refine ⟨12915780558861222060874787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8610520372574148040583191 12915780558861222060874787)
            ·
              refine ⟨19373670838291833091312181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12915780558861222060874787 19373670838291833091312181)
              ·
                refine ⟨1816281641089859352310517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19373670838291833091312181 1816281641089859352310517)
                ·
                  refine ⟨170276403852174314279111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1816281641089859352310517 170276403852174314279111)
                  ·
                    rfl

theorem cell23_2984509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_2984509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984509 prefixEnd_2984509 := by exact prefixLift 2984509
  have htrace : WordTrace (prefixWord ++ tailWord_2984509) baseStart_2984509 baseEnd_2984509 := by
    simpa [prefixWord, tailWord_2984509, baseEnd_2984509] using wordTrace_append hprefix tailTrace_2984509
  have hstable : (prefixWord ++ tailWord_2984509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984509).length < 2 ^ (prefixWord ++ tailWord_2984509).sum := by decide
  have hdescent : baseEnd_2984509 < baseStart_2984509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984515 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 5]
def baseStart_2984515 : Nat := 118140960795 + 2984515 * 2 ^ 59
def prefixEnd_2984515 : Nat := 4983230072969 + 3 ^ 40 * 2984515 * 2
def baseEnd_2984515 : Nat := 1532490715553495805036971

theorem tailTrace_2984515 : CollatzResearch.WordTrace tailWord_2984515 prefixEnd_2984515 1532490715553495805036971 := by
  unfold tailWord_2984515
  simp only [CollatzResearch.WordTrace]
  refine ⟨108854204782619344426658999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72569469855079562951105999 108854204782619344426658999)
  ·
    refine ⟨163281307173929016639988499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108854204782619344426658999 163281307173929016639988499)
    ·
      refine ⟨244921960760893524959982749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163281307173929016639988499 244921960760893524959982749)
      ·
        refine ⟨91845735285335071859993531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244921960760893524959982749 91845735285335071859993531)
        ·
          refine ⟨137768602928002607789990297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91845735285335071859993531 137768602928002607789990297)
          ·
            refine ⟨103326452196001955842492723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137768602928002607789990297 103326452196001955842492723)
            ·
              refine ⟨154989678294002933763739085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103326452196001955842492723 154989678294002933763739085)
              ·
                refine ⟨58121129360251100161402157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154989678294002933763739085 58121129360251100161402157)
                ·
                  refine ⟨21795423510094162560525809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58121129360251100161402157 21795423510094162560525809)
                  ·
                    refine ⟨16346567632570621920394357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21795423510094162560525809 16346567632570621920394357)
                    ·
                      refine ⟨1532490715553495805036971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16346567632570621920394357 1532490715553495805036971)
                      ·
                        rfl

theorem cell23_2984515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_2984515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984515 prefixEnd_2984515 := by exact prefixLift 2984515
  have htrace : WordTrace (prefixWord ++ tailWord_2984515) baseStart_2984515 baseEnd_2984515 := by
    simpa [prefixWord, tailWord_2984515, baseEnd_2984515] using wordTrace_append hprefix tailTrace_2984515
  have hstable : (prefixWord ++ tailWord_2984515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984515).length < 2 ^ (prefixWord ++ tailWord_2984515).sum := by decide
  have hdescent : baseEnd_2984515 < baseStart_2984515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984555 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 6]
def baseStart_2984555 : Nat := 118140960795 + 2984555 * 2 ^ 59
def prefixEnd_2984555 : Nat := 4983230072969 + 3 ^ 40 * 2984555 * 2
def baseEnd_2984555 : Nat := 1532511254779675648536787

theorem tailTrace_2984555 : CollatzResearch.WordTrace tailWord_2984555 prefixEnd_2984555 1532511254779675648536787 := by
  unfold tailWord_2984555
  simp only [CollatzResearch.WordTrace]
  refine ⟨108855663702474431258115119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72570442468316287505410079 108855663702474431258115119)
  ·
    refine ⟨163283495553711646887172679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108855663702474431258115119 163283495553711646887172679)
    ·
      refine ⟨244925243330567470330759019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163283495553711646887172679 244925243330567470330759019)
      ·
        refine ⟨367387864995851205496138529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244925243330567470330759019 367387864995851205496138529)
        ·
          refine ⟨275540898746888404122103897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367387864995851205496138529 275540898746888404122103897)
          ·
            refine ⟨206655674060166303091577923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275540898746888404122103897 206655674060166303091577923)
            ·
              refine ⟨309983511090249454637366885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206655674060166303091577923 309983511090249454637366885)
              ·
                refine ⟨58121908329421772744506291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 309983511090249454637366885 58121908329421772744506291)
                ·
                  refine ⟨87182862494132659116759437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58121908329421772744506291 87182862494132659116759437)
                  ·
                    refine ⟨32693573435299747168784789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87182862494132659116759437 32693573435299747168784789)
                    ·
                      refine ⟨1532511254779675648536787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32693573435299747168784789 1532511254779675648536787)
                      ·
                        rfl

theorem cell23_2984555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 6].length) (baseStart_2984555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984555 prefixEnd_2984555 := by exact prefixLift 2984555
  have htrace : WordTrace (prefixWord ++ tailWord_2984555) baseStart_2984555 baseEnd_2984555 := by
    simpa [prefixWord, tailWord_2984555, baseEnd_2984555] using wordTrace_append hprefix tailTrace_2984555
  have hstable : (prefixWord ++ tailWord_2984555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984555).length < 2 ^ (prefixWord ++ tailWord_2984555).sum := by decide
  have hdescent : baseEnd_2984555 < baseStart_2984555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984636 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 2, 3, 2]
def baseStart_2984636 : Nat := 118140960795 + 2984636 * 2 ^ 59
def prefixEnd_2984636 : Nat := 4983230072969 + 3 ^ 40 * 2984636 * 2
def baseEnd_2984636 : Nat := 1532552846712689831623915

theorem tailTrace_2984636 : CollatzResearch.WordTrace tailWord_2984636 prefixEnd_2984636 1532552846712689831623915 := by
  unfold tailWord_2984636
  simp only [CollatzResearch.WordTrace]
  refine ⟨54429309007590491045906881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72572412010120654727875841 54429309007590491045906881)
  ·
    refine ⟨40821981755692868284430161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54429309007590491045906881 40821981755692868284430161)
    ·
      refine ⟨30616486316769651213322621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40821981755692868284430161 30616486316769651213322621)
      ·
        refine ⟨11481182368788619204995983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30616486316769651213322621 11481182368788619204995983)
        ·
          refine ⟨17221773553182928807493975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11481182368788619204995983 17221773553182928807493975)
          ·
            refine ⟨25832660329774393211240963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17221773553182928807493975 25832660329774393211240963)
            ·
              refine ⟨38748990494661589816861445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25832660329774393211240963 38748990494661589816861445)
              ·
                refine ⟨7265435717749048090661521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38748990494661589816861445 7265435717749048090661521)
                ·
                  refine ⟨5449076788311786067996141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7265435717749048090661521 5449076788311786067996141)
                  ·
                    refine ⟨2043403795616919775498553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5449076788311786067996141 2043403795616919775498553)
                    ·
                      refine ⟨1532552846712689831623915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2043403795616919775498553 1532552846712689831623915)
                      ·
                        rfl

theorem cell23_2984636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_2984636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984636 prefixEnd_2984636 := by exact prefixLift 2984636
  have htrace : WordTrace (prefixWord ++ tailWord_2984636) baseStart_2984636 baseEnd_2984636 := by
    simpa [prefixWord, tailWord_2984636, baseEnd_2984636] using wordTrace_append hprefix tailTrace_2984636
  have hstable : (prefixWord ++ tailWord_2984636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984636).length < 2 ^ (prefixWord ++ tailWord_2984636).sum := by decide
  have hdescent : baseEnd_2984636 < baseStart_2984636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984680 : List Nat := [2, 1, 4, 1, 5, 1, 2, 1, 1, 5]
def baseStart_2984680 : Nat := 118140960795 + 2984680 * 2 ^ 59
def prefixEnd_2984680 : Nat := 4983230072969 + 3 ^ 40 * 2984680 * 2
def baseEnd_2984680 : Nat := 510858479953829219824571

theorem tailTrace_2984680 : CollatzResearch.WordTrace tailWord_2984680 prefixEnd_2984680 510858479953829219824571 := by
  unfold tailWord_2984680
  simp only [CollatzResearch.WordTrace]
  refine ⟨54430111413510788803207747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72573481884681051737610329 54430111413510788803207747)
  ·
    refine ⟨81645167120266183204811621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54430111413510788803207747 81645167120266183204811621)
    ·
      refine ⟨15308468835049909350902179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81645167120266183204811621 15308468835049909350902179)
      ·
        refine ⟨22962703252574864026353269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15308468835049909350902179 22962703252574864026353269)
        ·
          refine ⟨2152753429928893502470619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22962703252574864026353269 2152753429928893502470619)
          ·
            refine ⟨3229130144893340253705929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152753429928893502470619 3229130144893340253705929)
            ·
              refine ⟨2421847608670005190279447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3229130144893340253705929 2421847608670005190279447)
              ·
                refine ⟨3632771413005007785419171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2421847608670005190279447 3632771413005007785419171)
                ·
                  refine ⟨5449157119507511678128757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632771413005007785419171 5449157119507511678128757)
                  ·
                    refine ⟨510858479953829219824571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5449157119507511678128757 510858479953829219824571)
                    ·
                      rfl

theorem cell23_2984680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_2984680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984680 prefixEnd_2984680 := by exact prefixLift 2984680
  have htrace : WordTrace (prefixWord ++ tailWord_2984680) baseStart_2984680 baseEnd_2984680 := by
    simpa [prefixWord, tailWord_2984680, baseEnd_2984680] using wordTrace_append hprefix tailTrace_2984680
  have hstable : (prefixWord ++ tailWord_2984680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984680).length < 2 ^ (prefixWord ++ tailWord_2984680).sum := by decide
  have hdescent : baseEnd_2984680 < baseStart_2984680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984700 : List Nat := [2, 2, 2, 1, 3, 2, 2, 4, 1, 2, 2]
def baseStart_2984700 : Nat := 118140960795 + 2984700 * 2 ^ 59
def prefixEnd_2984700 : Nat := 4983230072969 + 3 ^ 40 * 2984700 * 2
def baseEnd_2984700 : Nat := 1532585709474577581223621

theorem tailTrace_2984700 : CollatzResearch.WordTrace tailWord_2984700 prefixEnd_2984700 1532585709474577581223621 := by
  unfold tailWord_2984700
  simp only [CollatzResearch.WordTrace]
  refine ⟨54430476143474560511071777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72573968191299414014762369 54430476143474560511071777)
  ·
    refine ⟨40822857107605920383303833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54430476143474560511071777 40822857107605920383303833)
    ·
      refine ⟨30617142830704440287477875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40822857107605920383303833 30617142830704440287477875)
      ·
        refine ⟨45925714246056660431216813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30617142830704440287477875 45925714246056660431216813)
        ·
          refine ⟨17222142842271247661706305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45925714246056660431216813 17222142842271247661706305)
          ·
            refine ⟨12916607131703435746279729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17222142842271247661706305 12916607131703435746279729)
            ·
              refine ⟨9687455348777576809709797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12916607131703435746279729 9687455348777576809709797)
              ·
                refine ⟨1816397877895795651820587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9687455348777576809709797 1816397877895795651820587)
                ·
                  refine ⟨2724596816843693477730881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816397877895795651820587 2724596816843693477730881)
                  ·
                    refine ⟨2043447612632770108298161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2724596816843693477730881 2043447612632770108298161)
                    ·
                      refine ⟨1532585709474577581223621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2043447612632770108298161 1532585709474577581223621)
                      ·
                        rfl

theorem cell23_2984700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_2984700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984700 prefixEnd_2984700 := by exact prefixLift 2984700
  have htrace : WordTrace (prefixWord ++ tailWord_2984700) baseStart_2984700 baseEnd_2984700 := by
    simpa [prefixWord, tailWord_2984700, baseEnd_2984700] using wordTrace_append hprefix tailTrace_2984700
  have hstable : (prefixWord ++ tailWord_2984700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984700).length < 2 ^ (prefixWord ++ tailWord_2984700).sum := by decide
  have hdescent : baseEnd_2984700 < baseStart_2984700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984759 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 3]
def baseStart_2984759 : Nat := 118140960795 + 2984759 * 2 ^ 59
def prefixEnd_2984759 : Nat := 4983230072969 + 3 ^ 40 * 2984759 * 2
def baseEnd_2984759 : Nat := 1532616004833192850385849

theorem tailTrace_2984759 : CollatzResearch.WordTrace tailWord_2984759 prefixEnd_2984759 1532616004833192850385849 := by
  unfold tailWord_2984759
  simp only [CollatzResearch.WordTrace]
  refine ⟨108863104193735374098541331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72575402795823582732360887 108863104193735374098541331)
  ·
    refine ⟨163294656290603061147811997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108863104193735374098541331 163294656290603061147811997)
    ·
      refine ⟨61235496108976147930429499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163294656290603061147811997 61235496108976147930429499)
      ·
        refine ⟨91853244163464221895644249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61235496108976147930429499 91853244163464221895644249)
        ·
          refine ⟨68889933122598166421733187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91853244163464221895644249 68889933122598166421733187)
          ·
            refine ⟨103334899683897249632599781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68889933122598166421733187 103334899683897249632599781)
            ·
              refine ⟨19375293690730734306112459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103334899683897249632599781 19375293690730734306112459)
              ·
                refine ⟨29062940536096101459168689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19375293690730734306112459 29062940536096101459168689)
                ·
                  refine ⟨21797205402072076094376517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29062940536096101459168689 21797205402072076094376517)
                  ·
                    refine ⟨4086976012888514267695597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21797205402072076094376517 4086976012888514267695597)
                    ·
                      refine ⟨1532616004833192850385849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4086976012888514267695597 1532616004833192850385849)
                      ·
                        rfl

theorem cell23_2984759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_2984759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984759 prefixEnd_2984759 := by exact prefixLift 2984759
  have htrace : WordTrace (prefixWord ++ tailWord_2984759) baseStart_2984759 baseEnd_2984759 := by
    simpa [prefixWord, tailWord_2984759, baseEnd_2984759] using wordTrace_append hprefix tailTrace_2984759
  have hstable : (prefixWord ++ tailWord_2984759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984759).length < 2 ^ (prefixWord ++ tailWord_2984759).sum := by decide
  have hdescent : baseEnd_2984759 < baseStart_2984759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984816 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 2, 5, 2]
def baseStart_2984816 : Nat := 118140960795 + 2984816 * 2 ^ 59
def prefixEnd_2984816 : Nat := 4983230072969 + 3 ^ 40 * 2984816 * 2
def baseEnd_2984816 : Nat := 1532645273230499127373087

theorem tailTrace_2984816 : CollatzResearch.WordTrace tailWord_2984816 prefixEnd_2984816 1532645273230499127373087 := by
  unfold tailWord_2984816
  simp only [CollatzResearch.WordTrace]
  refine ⟨54432591577264436416683151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72576788769685915222244201 54432591577264436416683151)
  ·
    refine ⟨81648887365896654625024727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54432591577264436416683151 81648887365896654625024727)
    ·
      refine ⟨122473331048844981937537091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81648887365896654625024727 122473331048844981937537091)
      ·
        refine ⟨183709996573267472906305637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122473331048844981937537091 183709996573267472906305637)
        ·
          refine ⟨34445624357487651169932307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183709996573267472906305637 34445624357487651169932307)
          ·
            refine ⟨51668436536231476754898461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34445624357487651169932307 51668436536231476754898461)
            ·
              refine ⟨19375663701086803783086923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51668436536231476754898461 19375663701086803783086923)
              ·
                refine ⟨29063495551630205674630385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19375663701086803783086923 29063495551630205674630385)
                ·
                  refine ⟨21797621663722654255972789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29063495551630205674630385 21797621663722654255972789)
                  ·
                    refine ⟨2043527030973998836497449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21797621663722654255972789 2043527030973998836497449)
                    ·
                      refine ⟨1532645273230499127373087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2043527030973998836497449 1532645273230499127373087)
                      ·
                        rfl

theorem cell23_2984816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 2, 5, 2].length) (baseStart_2984816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984816 prefixEnd_2984816 := by exact prefixLift 2984816
  have htrace : WordTrace (prefixWord ++ tailWord_2984816) baseStart_2984816 baseEnd_2984816 := by
    simpa [prefixWord, tailWord_2984816, baseEnd_2984816] using wordTrace_append hprefix tailTrace_2984816
  have hstable : (prefixWord ++ tailWord_2984816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984816).length < 2 ^ (prefixWord ++ tailWord_2984816).sum := by decide
  have hdescent : baseEnd_2984816 < baseStart_2984816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984819 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 5]
def baseStart_2984819 : Nat := 118140960795 + 2984819 * 2 ^ 59
def prefixEnd_2984819 : Nat := 4983230072969 + 3 ^ 40 * 2984819 * 2
def baseEnd_2984819 : Nat := 1532646813672462615635573

theorem tailTrace_2984819 : CollatzResearch.WordTrace tailWord_2984819 prefixEnd_2984819 1532646813672462615635573 := by
  unfold tailWord_2984819
  simp only [CollatzResearch.WordTrace]
  refine ⟨108865292573518004345725511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72576861715678669563817007 108865292573518004345725511)
  ·
    refine ⟨163297938860277006518588267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108865292573518004345725511 163297938860277006518588267)
    ·
      refine ⟨244946908290415509777882401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163297938860277006518588267 244946908290415509777882401)
      ·
        refine ⟨183710181217811632333411801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244946908290415509777882401 183710181217811632333411801)
        ·
          refine ⟨137782635913358724250058851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183710181217811632333411801 137782635913358724250058851)
          ·
            refine ⟨206673953870038086375088277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137782635913358724250058851 206673953870038086375088277)
            ·
              refine ⟨9687841587658035298832263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 206673953870038086375088277 9687841587658035298832263)
              ·
                refine ⟨14531762381487052948248395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9687841587658035298832263 14531762381487052948248395)
                ·
                  refine ⟨21797643572230579422372593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14531762381487052948248395 21797643572230579422372593)
                  ·
                    refine ⟨16348232679172934566779445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21797643572230579422372593 16348232679172934566779445)
                    ·
                      refine ⟨1532646813672462615635573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16348232679172934566779445 1532646813672462615635573)
                      ·
                        rfl

theorem cell23_2984819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_2984819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984819 prefixEnd_2984819 := by exact prefixLift 2984819
  have htrace : WordTrace (prefixWord ++ tailWord_2984819) baseStart_2984819 baseEnd_2984819 := by
    simpa [prefixWord, tailWord_2984819, baseEnd_2984819] using wordTrace_append hprefix tailTrace_2984819
  have hstable : (prefixWord ++ tailWord_2984819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984819).length < 2 ^ (prefixWord ++ tailWord_2984819).sum := by decide
  have hdescent : baseEnd_2984819 < baseStart_2984819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984863 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 2, 4, 2]
def baseStart_2984863 : Nat := 118140960795 + 2984863 * 2 ^ 59
def prefixEnd_2984863 : Nat := 4983230072969 + 3 ^ 40 * 2984863 * 2
def baseEnd_2984863 : Nat := 1532669406821260443485371

theorem tailTrace_2984863 : CollatzResearch.WordTrace tailWord_2984863 prefixEnd_2984863 1532669406821260443485371 := by
  unfold tailWord_2984863
  simp only [CollatzResearch.WordTrace]
  refine ⟨108866897385358599860327243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72577931590239066573551495 108866897385358599860327243)
  ·
    refine ⟨163300346078037899790490865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108866897385358599860327243 163300346078037899790490865)
    ·
      refine ⟨122475259558528424842868149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163300346078037899790490865 122475259558528424842868149)
      ·
        refine ⟨11482055583612039829018889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122475259558528424842868149 11482055583612039829018889)
        ·
          refine ⟨8611541687709029871764167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11482055583612039829018889 8611541687709029871764167)
          ·
            refine ⟨12917312531563544807646251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8611541687709029871764167 12917312531563544807646251)
            ·
              refine ⟨19375968797345317211469377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12917312531563544807646251 19375968797345317211469377)
              ·
                refine ⟨14531976598008987908602033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19375968797345317211469377 14531976598008987908602033)
                ·
                  refine ⟨10898982448506740931451525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14531976598008987908602033 10898982448506740931451525)
                  ·
                    refine ⟨2043559209095013924647161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10898982448506740931451525 2043559209095013924647161)
                    ·
                      refine ⟨1532669406821260443485371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2043559209095013924647161 1532669406821260443485371)
                      ·
                        rfl

theorem cell23_2984863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_2984863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984863 prefixEnd_2984863 := by exact prefixLift 2984863
  have htrace : WordTrace (prefixWord ++ tailWord_2984863) baseStart_2984863 baseEnd_2984863 := by
    simpa [prefixWord, tailWord_2984863, baseEnd_2984863] using wordTrace_append hprefix tailTrace_2984863
  have hstable : (prefixWord ++ tailWord_2984863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984863).length < 2 ^ (prefixWord ++ tailWord_2984863).sum := by decide
  have hdescent : baseEnd_2984863 < baseStart_2984863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984873 : List Nat := [1, 2, 1, 1, 1, 1, 5, 6, 1, 4]
def baseStart_2984873 : Nat := 118140960795 + 2984873 * 2 ^ 59
def prefixEnd_2984873 : Nat := 4983230072969 + 3 ^ 40 * 2984873 * 2
def baseEnd_2984873 : Nat := 510891513875935134786775

theorem tailTrace_2984873 : CollatzResearch.WordTrace tailWord_2984873 prefixEnd_2984873 510891513875935134786775 := by
  unfold tailWord_2984873
  simp only [CollatzResearch.WordTrace]
  refine ⟨108867262115322371568191273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72578174743548247712127515 108867262115322371568191273)
  ·
    refine ⟨81650446586491778676143455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108867262115322371568191273 81650446586491778676143455)
    ·
      refine ⟨122475669879737668014215183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81650446586491778676143455 122475669879737668014215183)
      ·
        refine ⟨183713504819606502021322775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122475669879737668014215183 183713504819606502021322775)
        ·
          refine ⟨275570257229409753031984163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183713504819606502021322775 275570257229409753031984163)
          ·
            refine ⟨413355385844114629547976245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275570257229409753031984163 413355385844114629547976245)
            ·
              refine ⟨38752067422885746520122773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 413355385844114629547976245 38752067422885746520122773)
              ·
                refine ⟨1816503160447769368130755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38752067422885746520122773 1816503160447769368130755)
                ·
                  refine ⟨2724754740671654052196133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816503160447769368130755 2724754740671654052196133)
                  ·
                    refine ⟨510891513875935134786775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2724754740671654052196133 510891513875935134786775)
                    ·
                      rfl

theorem cell23_2984873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 1, 4].length) (baseStart_2984873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984873 prefixEnd_2984873 := by exact prefixLift 2984873
  have htrace : WordTrace (prefixWord ++ tailWord_2984873) baseStart_2984873 baseEnd_2984873 := by
    simpa [prefixWord, tailWord_2984873, baseEnd_2984873] using wordTrace_append hprefix tailTrace_2984873
  have hstable : (prefixWord ++ tailWord_2984873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984873).length < 2 ^ (prefixWord ++ tailWord_2984873).sum := by decide
  have hdescent : baseEnd_2984873 < baseStart_2984873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984950 : List Nat := [5, 1, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_2984950 : Nat := 118140960795 + 2984950 * 2 ^ 59
def prefixEnd_2984950 : Nat := 4983230072969 + 3 ^ 40 * 2984950 * 2
def baseEnd_2984950 : Nat := 510904693212733867699157

theorem tailTrace_2984950 : CollatzResearch.WordTrace tailWord_2984950 prefixEnd_2984950 510904693212733867699157 := by
  unfold tailWord_2984950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6804379408502713357421519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72580047024028942479162869 6804379408502713357421519)
  ·
    refine ⟨10206569112754070036132279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6804379408502713357421519 10206569112754070036132279)
    ·
      refine ⟨15309853669131105054198419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10206569112754070036132279 15309853669131105054198419)
      ·
        refine ⟨22964780503696657581297629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15309853669131105054198419 22964780503696657581297629)
        ·
          refine ⟨8611792688886246592986611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22964780503696657581297629 8611792688886246592986611)
          ·
            refine ⟨12917689033329369889479917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8611792688886246592986611 12917689033329369889479917)
            ·
              refine ⟨4844133387498513708554969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12917689033329369889479917 4844133387498513708554969)
              ·
                refine ⟨3633100040623885281416227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4844133387498513708554969 3633100040623885281416227)
                ·
                  refine ⟨5449650060935827922124341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3633100040623885281416227 5449650060935827922124341)
                  ·
                    refine ⟨510904693212733867699157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5449650060935827922124341 510904693212733867699157)
                    ·
                      rfl

theorem cell23_2984950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_2984950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984950 prefixEnd_2984950 := by exact prefixLift 2984950
  have htrace : WordTrace (prefixWord ++ tailWord_2984950) baseStart_2984950 baseEnd_2984950 := by
    simpa [prefixWord, tailWord_2984950, baseEnd_2984950] using wordTrace_append hprefix tailTrace_2984950
  have hstable : (prefixWord ++ tailWord_2984950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984950).length < 2 ^ (prefixWord ++ tailWord_2984950).sum := by decide
  have hdescent : baseEnd_2984950 < baseStart_2984950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2984993 : List Nat := [1, 2, 3, 2, 3, 3, 1, 8]
def baseStart_2984993 : Nat := 118140960795 + 2984993 * 2 ^ 59
def prefixEnd_2984993 : Nat := 4983230072969 + 3 ^ 40 * 2984993 * 2
def baseEnd_2984993 : Nat := 56768005900234997587399

theorem tailTrace_2984993 : CollatzResearch.WordTrace tailWord_2984993 prefixEnd_2984993 56768005900234997587399 := by
  unfold tailWord_2984993
  simp only [CollatzResearch.WordTrace]
  refine ⟨108871638874887632062559633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72581092583258421375039755 108871638874887632062559633)
  ·
    refine ⟨81653729156165724046919725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108871638874887632062559633 81653729156165724046919725)
    ·
      refine ⟨30620148433562146517594897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81653729156165724046919725 30620148433562146517594897)
      ·
        refine ⟨22965111325171609888196173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30620148433562146517594897 22965111325171609888196173)
        ·
          refine ⟨8611916746939353708073565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22965111325171609888196173 8611916746939353708073565)
          ·
            refine ⟨3229468780102257640527587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8611916746939353708073565 3229468780102257640527587)
            ·
              refine ⟨4844203170153386460791381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3229468780102257640527587 4844203170153386460791381)
              ·
                refine ⟨56768005900234997587399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4844203170153386460791381 56768005900234997587399)
                ·
                  rfl

theorem cell23_2984993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 8].length) (baseStart_2984993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2984993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2984993 prefixEnd_2984993 := by exact prefixLift 2984993
  have htrace : WordTrace (prefixWord ++ tailWord_2984993) baseStart_2984993 baseEnd_2984993 := by
    simpa [prefixWord, tailWord_2984993, baseEnd_2984993] using wordTrace_append hprefix tailTrace_2984993
  have hstable : (prefixWord ++ tailWord_2984993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2984993).length < 2 ^ (prefixWord ++ tailWord_2984993).sum := by decide
  have hdescent : baseEnd_2984993 < baseStart_2984993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2984993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985003 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 3]
def baseStart_2985003 : Nat := 118140960795 + 2985003 * 2 ^ 59
def prefixEnd_2985003 : Nat := 4983230072969 + 3 ^ 40 * 2985003 * 2
def baseEnd_2985003 : Nat := 1532741294112889895734727

theorem tailTrace_2985003 : CollatzResearch.WordTrace tailWord_2985003 prefixEnd_2985003 1532741294112889895734727 := by
  unfold tailWord_2985003
  simp only [CollatzResearch.WordTrace]
  refine ⟨108872003604851403770423663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72581335736567602513615775 108872003604851403770423663)
  ·
    refine ⟨163308005407277105655635495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108872003604851403770423663 163308005407277105655635495)
    ·
      refine ⟨244962008110915658483453243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163308005407277105655635495 244962008110915658483453243)
      ·
        refine ⟨367443012166373487725179865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244962008110915658483453243 367443012166373487725179865)
        ·
          refine ⟨275582259124780115793884899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367443012166373487725179865 275582259124780115793884899)
          ·
            refine ⟨413373388687170173690827349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275582259124780115793884899 413373388687170173690827349)
            ·
              refine ⟨4844219398677775472939383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 413373388687170173690827349 4844219398677775472939383)
              ·
                refine ⟨7266329098016663209409075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4844219398677775472939383 7266329098016663209409075)
                ·
                  refine ⟨10899493647024994814113613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7266329098016663209409075 10899493647024994814113613)
                  ·
                    refine ⟨4087310117634373055292605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10899493647024994814113613 4087310117634373055292605)
                    ·
                      refine ⟨1532741294112889895734727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4087310117634373055292605 1532741294112889895734727)
                      ·
                        rfl

theorem cell23_2985003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 3].length) (baseStart_2985003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985003 prefixEnd_2985003 := by exact prefixLift 2985003
  have htrace : WordTrace (prefixWord ++ tailWord_2985003) baseStart_2985003 baseEnd_2985003 := by
    simpa [prefixWord, tailWord_2985003, baseEnd_2985003] using wordTrace_append hprefix tailTrace_2985003
  have hstable : (prefixWord ++ tailWord_2985003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985003).length < 2 ^ (prefixWord ++ tailWord_2985003).sum := by decide
  have hdescent : baseEnd_2985003 < baseStart_2985003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985037 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_2985037 : Nat := 118140960795 + 2985037 * 2 ^ 59
def prefixEnd_2985037 : Nat := 4983230072969 + 3 ^ 40 * 2985037 * 2
def baseEnd_2985037 : Nat := 1532758752455142762709571

theorem tailTrace_2985037 : CollatzResearch.WordTrace tailWord_2985037 prefixEnd_2985037 1532758752455142762709571 := by
  unfold tailWord_2985037
  simp only [CollatzResearch.WordTrace]
  refine ⟨108873243686728227577161365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72582162457818818384774243 108873243686728227577161365)
  ·
    refine ⟨5103433297815385667679439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 108873243686728227577161365 5103433297815385667679439)
    ·
      refine ⟨7655149946723078501519159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5103433297815385667679439 7655149946723078501519159)
      ·
        refine ⟨11482724920084617752278739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7655149946723078501519159 11482724920084617752278739)
        ·
          refine ⟨17224087380126926628418109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11482724920084617752278739 17224087380126926628418109)
          ·
            refine ⟨6459032767547597485656791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17224087380126926628418109 6459032767547597485656791)
            ·
              refine ⟨9688549151321396228485187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6459032767547597485656791 9688549151321396228485187)
              ·
                refine ⟨14532823726982094342727781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9688549151321396228485187 14532823726982094342727781)
                ·
                  refine ⟨2724904448809142689261459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14532823726982094342727781 2724904448809142689261459)
                  ·
                    refine ⟨4087356673213714033892189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2724904448809142689261459 4087356673213714033892189)
                    ·
                      refine ⟨1532758752455142762709571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4087356673213714033892189 1532758752455142762709571)
                      ·
                        rfl

theorem cell23_2985037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_2985037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985037 prefixEnd_2985037 := by exact prefixLift 2985037
  have htrace : WordTrace (prefixWord ++ tailWord_2985037) baseStart_2985037 baseEnd_2985037 := by
    simpa [prefixWord, tailWord_2985037, baseEnd_2985037] using wordTrace_append hprefix tailTrace_2985037
  have hstable : (prefixWord ++ tailWord_2985037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985037).length < 2 ^ (prefixWord ++ tailWord_2985037).sum := by decide
  have hdescent : baseEnd_2985037 < baseStart_2985037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985043 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 5, 4, 2]
def baseStart_2985043 : Nat := 118140960795 + 2985043 * 2 ^ 59
def prefixEnd_2985043 : Nat := 4983230072969 + 3 ^ 40 * 2985043 * 2
def baseEnd_2985043 : Nat := 1532761833339069739234543

theorem tailTrace_2985043 : CollatzResearch.WordTrace tailWord_2985043 prefixEnd_2985043 1532761833339069739234543 := by
  unfold tailWord_2985043
  simp only [CollatzResearch.WordTrace]
  refine ⟨108873462524706490601879783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72582308349804327067919855 108873462524706490601879783)
  ·
    refine ⟨163310193787059735902819675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108873462524706490601879783 163310193787059735902819675)
    ·
      refine ⟨244965290680589603854229513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163310193787059735902819675 244965290680589603854229513)
      ·
        refine ⟨183723968010442202890672135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244965290680589603854229513 183723968010442202890672135)
        ·
          refine ⟨275585952015663304336008203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183723968010442202890672135 275585952015663304336008203)
          ·
            refine ⟨413378928023494956504012305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275585952015663304336008203 413378928023494956504012305)
            ·
              refine ⟨310034196017621217378009229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413378928023494956504012305 310034196017621217378009229)
              ·
                refine ⟨116262823506607956516753461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310034196017621217378009229 116262823506607956516753461)
                ·
                  refine ⟨10899639703744495923445637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116262823506607956516753461 10899639703744495923445637)
                  ·
                    refine ⟨2043682444452092985646057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10899639703744495923445637 2043682444452092985646057)
                    ·
                      refine ⟨1532761833339069739234543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2043682444452092985646057 1532761833339069739234543)
                      ·
                        rfl

theorem cell23_2985043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 4, 2].length) (baseStart_2985043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985043 prefixEnd_2985043 := by exact prefixLift 2985043
  have htrace : WordTrace (prefixWord ++ tailWord_2985043) baseStart_2985043 baseEnd_2985043 := by
    simpa [prefixWord, tailWord_2985043, baseEnd_2985043] using wordTrace_append hprefix tailTrace_2985043
  have hstable : (prefixWord ++ tailWord_2985043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985043).length < 2 ^ (prefixWord ++ tailWord_2985043).sum := by decide
  have hdescent : baseEnd_2985043 < baseStart_2985043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985054 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_2985054 : Nat := 118140960795 + 2985054 * 2 ^ 59
def prefixEnd_2985054 : Nat := 4983230072969 + 3 ^ 40 * 2985054 * 2
def baseEnd_2985054 : Nat := 1532767481626269196196993

theorem tailTrace_2985054 : CollatzResearch.WordTrace tailWord_2985054 prefixEnd_2985054 1532767481626269196196993 := by
  unfold tailWord_2985054
  simp only [CollatzResearch.WordTrace]
  refine ⟨13609232965958329935066277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72582575818444426320353477 13609232965958329935066277)
  ·
    refine ⟨2551731181117186862824927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13609232965958329935066277 2551731181117186862824927)
    ·
      refine ⟨3827596771675780294237391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2551731181117186862824927 3827596771675780294237391)
      ·
        refine ⟨5741395157513670441356087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3827596771675780294237391 5741395157513670441356087)
        ·
          refine ⟨8612092736270505662034131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5741395157513670441356087 8612092736270505662034131)
          ·
            refine ⟨12918139104405758493051197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8612092736270505662034131 12918139104405758493051197)
            ·
              refine ⟨4844302164152159434894199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12918139104405758493051197 4844302164152159434894199)
              ·
                refine ⟨7266453246228239152341299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4844302164152159434894199 7266453246228239152341299)
                ·
                  refine ⟨10899679869342358728511949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7266453246228239152341299 10899679869342358728511949)
                  ·
                    refine ⟨4087379951003384523191981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10899679869342358728511949 4087379951003384523191981)
                    ·
                      refine ⟨1532767481626269196196993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4087379951003384523191981 1532767481626269196196993)
                      ·
                        rfl

theorem cell23_2985054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_2985054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985054 prefixEnd_2985054 := by exact prefixLift 2985054
  have htrace : WordTrace (prefixWord ++ tailWord_2985054) baseStart_2985054 baseEnd_2985054 := by
    simpa [prefixWord, tailWord_2985054, baseEnd_2985054] using wordTrace_append hprefix tailTrace_2985054
  have hstable : (prefixWord ++ tailWord_2985054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985054).length < 2 ^ (prefixWord ++ tailWord_2985054).sum := by decide
  have hdescent : baseEnd_2985054 < baseStart_2985054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985111 : List Nat := [1, 1, 3, 3, 3, 3, 2, 1, 2, 2, 2]
def baseStart_2985111 : Nat := 118140960795 + 2985111 * 2 ^ 59
def prefixEnd_2985111 : Nat := 4983230072969 + 3 ^ 40 * 2985111 * 2
def baseEnd_2985111 : Nat := 1532796750023575473184231

theorem tailTrace_2985111 : CollatzResearch.WordTrace tailWord_2985111 prefixEnd_2985111 1532796750023575473184231 := by
  unfold tailWord_2985111
  simp only [CollatzResearch.WordTrace]
  refine ⟨108875942688460138215355187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72583961792306758810236791 108875942688460138215355187)
  ·
    refine ⟨163313914032690207323032781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108875942688460138215355187 163313914032690207323032781)
    ·
      refine ⟨61242717762258827746137293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163313914032690207323032781 61242717762258827746137293)
      ·
        refine ⟨22966019160847060404801485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61242717762258827746137293 22966019160847060404801485)
        ·
          refine ⟨8612257185317647651800557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22966019160847060404801485 8612257185317647651800557)
          ·
            refine ⟨3229596444494117869425209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8612257185317647651800557 3229596444494117869425209)
            ·
              refine ⟨2422197333370588402068907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3229596444494117869425209 2422197333370588402068907)
              ·
                refine ⟨3633296000055882603103361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2422197333370588402068907 3633296000055882603103361)
                ·
                  refine ⟨2724972000041911952327521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3633296000055882603103361 2724972000041911952327521)
                  ·
                    refine ⟨2043729000031433964245641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2724972000041911952327521 2043729000031433964245641)
                    ·
                      refine ⟨1532796750023575473184231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2043729000031433964245641 1532796750023575473184231)
                      ·
                        rfl

theorem cell23_2985111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_2985111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985111 prefixEnd_2985111 := by exact prefixLift 2985111
  have htrace : WordTrace (prefixWord ++ tailWord_2985111) baseStart_2985111 baseEnd_2985111 := by
    simpa [prefixWord, tailWord_2985111, baseEnd_2985111] using wordTrace_append hprefix tailTrace_2985111
  have hstable : (prefixWord ++ tailWord_2985111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985111).length < 2 ^ (prefixWord ++ tailWord_2985111).sum := by decide
  have hdescent : baseEnd_2985111 < baseStart_2985111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985170 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_2985170 : Nat := 118140960795 + 2985170 * 2 ^ 59
def prefixEnd_2985170 : Nat := 4983230072969 + 3 ^ 40 * 2985170 * 2
def baseEnd_2985170 : Nat := 1532827045382190742346459

theorem tailTrace_2985170 : CollatzResearch.WordTrace tailWord_2985170 prefixEnd_2985170 1532827045382190742346459 := by
  unfold tailWord_2985170
  simp only [CollatzResearch.WordTrace]
  refine ⟨27219523648811597822938241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72585396396830927527835309 27219523648811597822938241)
  ·
    refine ⟨20414642736608698367203681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27219523648811597822938241 20414642736608698367203681)
    ·
      refine ⟨15310982052456523775402761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20414642736608698367203681 15310982052456523775402761)
      ·
        refine ⟨11483236539342392831552071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15310982052456523775402761 11483236539342392831552071)
        ·
          refine ⟨17224854809013589247328107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11483236539342392831552071 17224854809013589247328107)
          ·
            refine ⟨25837282213520383870992161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17224854809013589247328107 25837282213520383870992161)
            ·
              refine ⟨19377961660140287903244121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25837282213520383870992161 19377961660140287903244121)
              ·
                refine ⟨14533471245105215927433091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19377961660140287903244121 14533471245105215927433091)
                ·
                  refine ⟨21800206867657823891149637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14533471245105215927433091 21800206867657823891149637)
                  ·
                    refine ⟨4087538787685841979590557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21800206867657823891149637 4087538787685841979590557)
                    ·
                      refine ⟨1532827045382190742346459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4087538787685841979590557 1532827045382190742346459)
                      ·
                        rfl

theorem cell23_2985170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_2985170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985170 prefixEnd_2985170 := by exact prefixLift 2985170
  have htrace : WordTrace (prefixWord ++ tailWord_2985170) baseStart_2985170 baseEnd_2985170 := by
    simpa [prefixWord, tailWord_2985170, baseEnd_2985170] using wordTrace_append hprefix tailTrace_2985170
  have hstable : (prefixWord ++ tailWord_2985170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985170).length < 2 ^ (prefixWord ++ tailWord_2985170).sum := by decide
  have hdescent : baseEnd_2985170 < baseStart_2985170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985194 : List Nat := [3, 1, 3, 1, 1, 4, 2, 3, 1, 4]
def baseStart_2985194 : Nat := 118140960795 + 2985194 * 2 ^ 59
def prefixEnd_2985194 : Nat := 4983230072969 + 3 ^ 40 * 2985194 * 2
def baseEnd_2985194 : Nat := 510946456305966216148783

theorem tailTrace_2985194 : CollatzResearch.WordTrace tailWord_2985194 prefixEnd_2985194 510946456305966216148783 := by
  unfold tailWord_2985194
  simp only [CollatzResearch.WordTrace]
  refine ⟨27219742486789860847656659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72585979964772962260417757 27219742486789860847656659)
  ·
    refine ⟨40829613730184791271484989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27219742486789860847656659 40829613730184791271484989)
    ·
      refine ⟨15311105148819296726806871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40829613730184791271484989 15311105148819296726806871)
      ·
        refine ⟨22966657723228945090210307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15311105148819296726806871 22966657723228945090210307)
        ·
          refine ⟨34449986584843417635315461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22966657723228945090210307 34449986584843417635315461)
          ·
            refine ⟨6459372484658140806621649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34449986584843417635315461 6459372484658140806621649)
            ·
              refine ⟨4844529363493605604966237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6459372484658140806621649 4844529363493605604966237)
              ·
                refine ⟨1816698511310102101862339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4844529363493605604966237 1816698511310102101862339)
                ·
                  refine ⟨2725047766965153152793509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816698511310102101862339 2725047766965153152793509)
                  ·
                    refine ⟨510946456305966216148783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2725047766965153152793509 510946456305966216148783)
                    ·
                      rfl

theorem cell23_2985194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_2985194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985194 prefixEnd_2985194 := by exact prefixLift 2985194
  have htrace : WordTrace (prefixWord ++ tailWord_2985194) baseStart_2985194 baseEnd_2985194 := by
    simpa [prefixWord, tailWord_2985194, baseEnd_2985194] using wordTrace_append hprefix tailTrace_2985194
  have hstable : (prefixWord ++ tailWord_2985194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985194).length < 2 ^ (prefixWord ++ tailWord_2985194).sum := by decide
  have hdescent : baseEnd_2985194 < baseStart_2985194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985217 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_2985217 : Nat := 118140960795 + 2985217 * 2 ^ 59
def prefixEnd_2985217 : Nat := 4983230072969 + 3 ^ 40 * 2985217 * 2
def baseEnd_2985217 : Nat := 1532851178972952058458743

theorem tailTrace_2985217 : CollatzResearch.WordTrace tailWord_2985217 prefixEnd_2985217 1532851178972952058458743 := by
  unfold tailWord_2985217
  simp only [CollatzResearch.WordTrace]
  refine ⟨108879808826076118318713905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72586539217384078879142603 108879808826076118318713905)
  ·
    refine ⟨81659856619557088739035429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108879808826076118318713905 81659856619557088739035429)
    ·
      refine ⟨15311223116166954138569143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81659856619557088739035429 15311223116166954138569143)
      ·
        refine ⟨22966834674250431207853715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15311223116166954138569143 22966834674250431207853715)
        ·
          refine ⟨34450252011375646811780573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22966834674250431207853715 34450252011375646811780573)
          ·
            refine ⟨12918844504265867554417715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34450252011375646811780573 12918844504265867554417715)
            ·
              refine ⟨19378266756398801331626573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12918844504265867554417715 19378266756398801331626573)
              ·
                refine ⟨7266850033649550499359965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19378266756398801331626573 7266850033649550499359965)
                ·
                  refine ⟨2725068762618581437259987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7266850033649550499359965 2725068762618581437259987)
                  ·
                    refine ⟨4087603143927872155889981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2725068762618581437259987 4087603143927872155889981)
                    ·
                      refine ⟨1532851178972952058458743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4087603143927872155889981 1532851178972952058458743)
                      ·
                        rfl

theorem cell23_2985217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_2985217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985217 prefixEnd_2985217 := by exact prefixLift 2985217
  have htrace : WordTrace (prefixWord ++ tailWord_2985217) baseStart_2985217 baseEnd_2985217 := by
    simpa [prefixWord, tailWord_2985217, baseEnd_2985217] using wordTrace_append hprefix tailTrace_2985217
  have hstable : (prefixWord ++ tailWord_2985217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985217).length < 2 ^ (prefixWord ++ tailWord_2985217).sum := by decide
  have hdescent : baseEnd_2985217 < baseStart_2985217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985243 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 5]
def baseStart_2985243 : Nat := 118140960795 + 2985243 * 2 ^ 59
def prefixEnd_2985243 : Nat := 4983230072969 + 3 ^ 40 * 2985243 * 2
def baseEnd_2985243 : Nat := 1532864529469968956733623

theorem tailTrace_2985243 : CollatzResearch.WordTrace tailWord_2985243 prefixEnd_2985243 1532864529469968956733623 := by
  unfold tailWord_2985243
  simp only [CollatzResearch.WordTrace]
  refine ⟨108880757123981924759160383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72587171415987949839440255 108880757123981924759160383)
  ·
    refine ⟨163321135685972887138740575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108880757123981924759160383 163321135685972887138740575)
    ·
      refine ⟨244981703528959330708110863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163321135685972887138740575 244981703528959330708110863)
      ·
        refine ⟨367472555293438996062166295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244981703528959330708110863 367472555293438996062166295)
        ·
          refine ⟨551208832940158494093249443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367472555293438996062166295 551208832940158494093249443)
          ·
            refine ⟨826813249410237741139874165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551208832940158494093249443 826813249410237741139874165)
            ·
              refine ⟨77513742132209788231863203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 826813249410237741139874165 77513742132209788231863203)
              ·
                refine ⟨116270613198314682347794805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77513742132209788231863203 116270613198314682347794805)
                ·
                  refine ⟨10900369987342001470105763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116270613198314682347794805 10900369987342001470105763)
                  ·
                    refine ⟨16350554981013002205158645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10900369987342001470105763 16350554981013002205158645)
                    ·
                      refine ⟨1532864529469968956733623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16350554981013002205158645 1532864529469968956733623)
                      ·
                        rfl

theorem cell23_2985243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 5].length) (baseStart_2985243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985243 prefixEnd_2985243 := by exact prefixLift 2985243
  have htrace : WordTrace (prefixWord ++ tailWord_2985243) baseStart_2985243 baseEnd_2985243 := by
    simpa [prefixWord, tailWord_2985243, baseEnd_2985243] using wordTrace_append hprefix tailTrace_2985243
  have hstable : (prefixWord ++ tailWord_2985243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985243).length < 2 ^ (prefixWord ++ tailWord_2985243).sum := by decide
  have hdescent : baseEnd_2985243 < baseStart_2985243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985251 : List Nat := [1, 1, 1, 4, 2, 5, 1, 3, 1, 1, 3]
def baseStart_2985251 : Nat := 118140960795 + 2985251 * 2 ^ 59
def prefixEnd_2985251 : Nat := 4983230072969 + 3 ^ 40 * 2985251 * 2
def baseEnd_2985251 : Nat := 1532868637315204925433587

theorem tailTrace_2985251 : CollatzResearch.WordTrace tailWord_2985251 prefixEnd_2985251 1532868637315204925433587 := by
  unfold tailWord_2985251
  simp only [CollatzResearch.WordTrace]
  refine ⟨108881048907952942125451607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72587365938635294750301071 108881048907952942125451607)
  ·
    refine ⟨163321573361929413188177411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108881048907952942125451607 163321573361929413188177411)
    ·
      refine ⟨244982360042894119782266117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163321573361929413188177411 244982360042894119782266117)
      ·
        refine ⟨45934192508042647459174897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244982360042894119782266117 45934192508042647459174897)
        ·
          refine ⟨34450644381031985594381173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45934192508042647459174897 34450644381031985594381173)
          ·
            refine ⟨3229747910721748649473235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34450644381031985594381173 3229747910721748649473235)
            ·
              refine ⟨4844621866082622974209853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3229747910721748649473235 4844621866082622974209853)
              ·
                refine ⟨1816733199780983615328695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4844621866082622974209853 1816733199780983615328695)
                ·
                  refine ⟨2725099799671475422993043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816733199780983615328695 2725099799671475422993043)
                  ·
                    refine ⟨4087649699507213134489565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2725099799671475422993043 4087649699507213134489565)
                    ·
                      refine ⟨1532868637315204925433587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4087649699507213134489565 1532868637315204925433587)
                      ·
                        rfl

theorem cell23_2985251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_2985251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985251 prefixEnd_2985251 := by exact prefixLift 2985251
  have htrace : WordTrace (prefixWord ++ tailWord_2985251) baseStart_2985251 baseEnd_2985251 := by
    simpa [prefixWord, tailWord_2985251, baseEnd_2985251] using wordTrace_append hprefix tailTrace_2985251
  have hstable : (prefixWord ++ tailWord_2985251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985251).length < 2 ^ (prefixWord ++ tailWord_2985251).sum := by decide
  have hdescent : baseEnd_2985251 < baseStart_2985251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985260 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 3]
def baseStart_2985260 : Nat := 118140960795 + 2985260 * 2 ^ 59
def prefixEnd_2985260 : Nat := 4983230072969 + 3 ^ 40 * 2985260 * 2
def baseEnd_2985260 : Nat := 1532873258641095390221045

theorem tailTrace_2985260 : CollatzResearch.WordTrace tailWord_2985260 prefixEnd_2985260 1532873258641095390221045 := by
  unfold tailWord_2985260
  simp only [CollatzResearch.WordTrace]
  refine ⟨54440688582460168331264617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72587584776613557775019489 54440688582460168331264617)
  ·
    refine ⟨40830516436845126248448463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54440688582460168331264617 40830516436845126248448463)
    ·
      refine ⟨61245774655267689372672695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40830516436845126248448463 61245774655267689372672695)
      ·
        refine ⟨91868661982901534059009043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61245774655267689372672695 91868661982901534059009043)
        ·
          refine ⟨137802992974352301088513565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91868661982901534059009043 137802992974352301088513565)
          ·
            refine ⟨51676122365382112908192587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137802992974352301088513565 51676122365382112908192587)
            ·
              refine ⟨77514183548073169362288881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51676122365382112908192587 77514183548073169362288881)
              ·
                refine ⟨58135637661054877021716661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77514183548073169362288881 58135637661054877021716661)
                ·
                  refine ⟨5450216030723894720785937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58135637661054877021716661 5450216030723894720785937)
                  ·
                    refine ⟨4087662023042921040589453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5450216030723894720785937 4087662023042921040589453)
                    ·
                      refine ⟨1532873258641095390221045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4087662023042921040589453 1532873258641095390221045)
                      ·
                        rfl

theorem cell23_2985260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_2985260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985260 prefixEnd_2985260 := by exact prefixLift 2985260
  have htrace : WordTrace (prefixWord ++ tailWord_2985260) baseStart_2985260 baseEnd_2985260 := by
    simpa [prefixWord, tailWord_2985260, baseEnd_2985260] using wordTrace_append hprefix tailTrace_2985260
  have hstable : (prefixWord ++ tailWord_2985260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985260).length < 2 ^ (prefixWord ++ tailWord_2985260).sum := by decide
  have hdescent : baseEnd_2985260 < baseStart_2985260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985261 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_2985261 : Nat := 118140960795 + 2985261 * 2 ^ 59
def prefixEnd_2985261 : Nat := 4983230072969 + 3 ^ 40 * 2985261 * 2
def baseEnd_2985261 : Nat := 1532873772121749886308541

theorem tailTrace_2985261 : CollatzResearch.WordTrace tailWord_2985261 prefixEnd_2985261 1532873772121749886308541 := by
  unfold tailWord_2985261
  simp only [CollatzResearch.WordTrace]
  refine ⟨108881413637916713833315637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72587609091944475888877091 108881413637916713833315637)
  ·
    refine ⟨10207632528554691921873341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108881413637916713833315637 10207632528554691921873341)
    ·
      refine ⟨3827862198208009470702503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10207632528554691921873341 3827862198208009470702503)
      ·
        refine ⟨5741793297312014206053755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3827862198208009470702503 5741793297312014206053755)
        ·
          refine ⟨8612689945968021309080633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5741793297312014206053755 8612689945968021309080633)
          ·
            refine ⟨6459517459476015981810475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8612689945968021309080633 6459517459476015981810475)
            ·
              refine ⟨9689276189214023972715713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6459517459476015981810475 9689276189214023972715713)
              ·
                refine ⟨7266957141910517979536785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9689276189214023972715713 7266957141910517979536785)
                ·
                  refine ⟨5450217856432888484652589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7266957141910517979536785 5450217856432888484652589)
                  ·
                    refine ⟨2043831696162333181744721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5450217856432888484652589 2043831696162333181744721)
                    ·
                      refine ⟨1532873772121749886308541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2043831696162333181744721 1532873772121749886308541)
                      ·
                        rfl

theorem cell23_2985261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_2985261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985261 prefixEnd_2985261 := by exact prefixLift 2985261
  have htrace : WordTrace (prefixWord ++ tailWord_2985261) baseStart_2985261 baseEnd_2985261 := by
    simpa [prefixWord, tailWord_2985261, baseEnd_2985261] using wordTrace_append hprefix tailTrace_2985261
  have hstable : (prefixWord ++ tailWord_2985261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985261).length < 2 ^ (prefixWord ++ tailWord_2985261).sum := by decide
  have hdescent : baseEnd_2985261 < baseStart_2985261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985268 : List Nat := [2, 5, 1, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_2985268 : Nat := 118140960795 + 2985268 * 2 ^ 59
def prefixEnd_2985268 : Nat := 4983230072969 + 3 ^ 40 * 2985268 * 2
def baseEnd_2985268 : Nat := 1532877366486331358921009

theorem tailTrace_2985268 : CollatzResearch.WordTrace tailWord_2985268 prefixEnd_2985268 1532877366486331358921009 := by
  unfold tailWord_2985268
  simp only [CollatzResearch.WordTrace]
  refine ⟨54440834474445677014410229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72587779299260902685880305 54440834474445677014410229)
  ·
    refine ⟨5103828231979282220100959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54440834474445677014410229 5103828231979282220100959)
    ·
      refine ⟨7655742347968923330151439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5103828231979282220100959 7655742347968923330151439)
      ·
        refine ⟨11483613521953384995227159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7655742347968923330151439 11483613521953384995227159)
        ·
          refine ⟨17225420282930077492840739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11483613521953384995227159 17225420282930077492840739)
          ·
            refine ⟨25838130424395116239261109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17225420282930077492840739 25838130424395116239261109)
            ·
              refine ⟨2422324727287042147430729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25838130424395116239261109 2422324727287042147430729)
              ·
                refine ⟨1816743545465281610573047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2422324727287042147430729 1816743545465281610573047)
                ·
                  refine ⟨2725115318197922415859571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816743545465281610573047 2725115318197922415859571)
                  ·
                    refine ⟨4087672977296883623789357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2725115318197922415859571 4087672977296883623789357)
                    ·
                      refine ⟨1532877366486331358921009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4087672977296883623789357 1532877366486331358921009)
                      ·
                        rfl

theorem cell23_2985268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_2985268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985268 prefixEnd_2985268 := by exact prefixLift 2985268
  have htrace : WordTrace (prefixWord ++ tailWord_2985268) baseStart_2985268 baseEnd_2985268 := by
    simpa [prefixWord, tailWord_2985268, baseEnd_2985268] using wordTrace_append hprefix tailTrace_2985268
  have hstable : (prefixWord ++ tailWord_2985268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985268).length < 2 ^ (prefixWord ++ tailWord_2985268).sum := by decide
  have hdescent : baseEnd_2985268 < baseStart_2985268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985283 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 6]
def baseStart_2985283 : Nat := 118140960795 + 2985283 * 2 ^ 59
def prefixEnd_2985283 : Nat := 4983230072969 + 3 ^ 40 * 2985283 * 2
def baseEnd_2985283 : Nat := 1532885068696148800233439

theorem tailTrace_2985283 : CollatzResearch.WordTrace tailWord_2985283 prefixEnd_2985283 1532885068696148800233439 := by
  unfold tailWord_2985283
  simp only [CollatzResearch.WordTrace]
  refine ⟨108882216043837011590616503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72588144029224674393744335 108882216043837011590616503)
  ·
    refine ⟨163323324065755517385924755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108882216043837011590616503 163323324065755517385924755)
    ·
      refine ⟨244984986098633276078887133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163323324065755517385924755 244984986098633276078887133)
      ·
        refine ⟨91869369786987478529582675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244984986098633276078887133 91869369786987478529582675)
        ·
          refine ⟨137804054680481217794374013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91869369786987478529582675 137804054680481217794374013)
          ·
            refine ⟨51676520505180456672890255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137804054680481217794374013 51676520505180456672890255)
            ·
              refine ⟨77514780757770685009335383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51676520505180456672890255 77514780757770685009335383)
              ·
                refine ⟨116272171136656027514003075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77514780757770685009335383 116272171136656027514003075)
                ·
                  refine ⟨174408256704984041271004613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116272171136656027514003075 174408256704984041271004613)
                  ·
                    refine ⟨32701548132184507738313365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 174408256704984041271004613 32701548132184507738313365)
                    ·
                      refine ⟨1532885068696148800233439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32701548132184507738313365 1532885068696148800233439)
                      ·
                        rfl

theorem cell23_2985283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_2985283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985283 prefixEnd_2985283 := by exact prefixLift 2985283
  have htrace : WordTrace (prefixWord ++ tailWord_2985283) baseStart_2985283 baseEnd_2985283 := by
    simpa [prefixWord, tailWord_2985283, baseEnd_2985283] using wordTrace_append hprefix tailTrace_2985283
  have hstable : (prefixWord ++ tailWord_2985283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985283).length < 2 ^ (prefixWord ++ tailWord_2985283).sum := by decide
  have hdescent : baseEnd_2985283 < baseStart_2985283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985290 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 5, 3, 3]
def baseStart_2985290 : Nat := 118140960795 + 2985290 * 2 ^ 59
def prefixEnd_2985290 : Nat := 4983230072969 + 3 ^ 40 * 2985290 * 2
def baseEnd_2985290 : Nat := 1532888663060730272845907

theorem tailTrace_2985290 : CollatzResearch.WordTrace tailWord_2985290 prefixEnd_2985290 1532888663060730272845907 := by
  unfold tailWord_2985290
  simp only [CollatzResearch.WordTrace]
  refine ⟨27220617838702912946530331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72588314236541101190747549 27220617838702912946530331)
  ·
    refine ⟨40830926758054369419795497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27220617838702912946530331 40830926758054369419795497)
    ·
      refine ⟨30623195068540777064846623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40830926758054369419795497 30623195068540777064846623)
      ·
        refine ⟨45934792602811165597269935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30623195068540777064846623 45934792602811165597269935)
        ·
          refine ⟨68902188904216748395904903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45934792602811165597269935 68902188904216748395904903)
          ·
            refine ⟨103353283356325122593857355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68902188904216748395904903 103353283356325122593857355)
            ·
              refine ⟨155029925034487683890786033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103353283356325122593857355 155029925034487683890786033)
              ·
                refine ⟨116272443775865762918089525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155029925034487683890786033 116272443775865762918089525)
                ·
                  refine ⟨10900541603987415273570893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116272443775865762918089525 10900541603987415273570893)
                  ·
                    refine ⟨4087703101495280727589085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10900541603987415273570893 4087703101495280727589085)
                    ·
                      refine ⟨1532888663060730272845907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4087703101495280727589085 1532888663060730272845907)
                      ·
                        rfl

theorem cell23_2985290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_2985290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985290 prefixEnd_2985290 := by exact prefixLift 2985290
  have htrace : WordTrace (prefixWord ++ tailWord_2985290) baseStart_2985290 baseEnd_2985290 := by
    simpa [prefixWord, tailWord_2985290, baseEnd_2985290] using wordTrace_append hprefix tailTrace_2985290
  have hstable : (prefixWord ++ tailWord_2985290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985290).length < 2 ^ (prefixWord ++ tailWord_2985290).sum := by decide
  have hdescent : baseEnd_2985290 < baseStart_2985290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985324 : List Nat := [2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 3]
def baseStart_2985324 : Nat := 118140960795 + 2985324 * 2 ^ 59
def prefixEnd_2985324 : Nat := 4983230072969 + 3 ^ 40 * 2985324 * 2
def baseEnd_2985324 : Nat := 1532906121402983139820751

theorem tailTrace_2985324 : CollatzResearch.WordTrace tailWord_2985324 prefixEnd_2985324 1532906121402983139820751 := by
  unfold tailWord_2985324
  simp only [CollatzResearch.WordTrace]
  refine ⟨54441855718344237796429513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72589140957792317061906017 54441855718344237796429513)
  ·
    refine ⟨40831391788758178347322135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54441855718344237796429513 40831391788758178347322135)
    ·
      refine ⟨61247087683137267520983203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40831391788758178347322135 61247087683137267520983203)
      ·
        refine ⟨91870631524705901281474805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61247087683137267520983203 91870631524705901281474805)
        ·
          refine ⟨8612871705441178245138263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91870631524705901281474805 8612871705441178245138263)
          ·
            refine ⟨12919307558161767367707395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8612871705441178245138263 12919307558161767367707395)
            ·
              refine ⟨19378961337242651051561093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12919307558161767367707395 19378961337242651051561093)
              ·
                refine ⟨3633555250732997072167705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19378961337242651051561093 3633555250732997072167705)
                ·
                  refine ⟨2725166438049747804125779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3633555250732997072167705 2725166438049747804125779)
                  ·
                    refine ⟨4087749657074621706188669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2725166438049747804125779 4087749657074621706188669)
                    ·
                      refine ⟨1532906121402983139820751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4087749657074621706188669 1532906121402983139820751)
                      ·
                        rfl

theorem cell23_2985324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 3].length) (baseStart_2985324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985324 prefixEnd_2985324 := by exact prefixLift 2985324
  have htrace : WordTrace (prefixWord ++ tailWord_2985324) baseStart_2985324 baseEnd_2985324 := by
    simpa [prefixWord, tailWord_2985324, baseEnd_2985324] using wordTrace_append hprefix tailTrace_2985324
  have hstable : (prefixWord ++ tailWord_2985324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985324).length < 2 ^ (prefixWord ++ tailWord_2985324).sum := by decide
  have hdescent : baseEnd_2985324 < baseStart_2985324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985325 : List Nat := [1, 5, 1, 1, 1, 5, 2, 2, 1, 2, 2]
def baseStart_2985325 : Nat := 118140960795 + 2985325 * 2 ^ 59
def prefixEnd_2985325 : Nat := 4983230072969 + 3 ^ 40 * 2985325 * 2
def baseEnd_2985325 : Nat := 1532906634883637635908247

theorem tailTrace_2985325 : CollatzResearch.WordTrace tailWord_2985325 prefixEnd_2985325 1532906634883637635908247 := by
  unfold tailWord_2985325
  simp only [CollatzResearch.WordTrace]
  refine ⟨108883747909684852763645429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72589165273123235175763619 108883747909684852763645429)
  ·
    refine ⟨10207851366532954946591759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108883747909684852763645429 10207851366532954946591759)
    ·
      refine ⟨15311777049799432419887639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10207851366532954946591759 15311777049799432419887639)
      ·
        refine ⟨22967665574699148629831459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15311777049799432419887639 22967665574699148629831459)
        ·
          refine ⟨34451498362048722944747189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22967665574699148629831459 34451498362048722944747189)
          ·
            refine ⟨3229827971442067776070049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34451498362048722944747189 3229827971442067776070049)
            ·
              refine ⟨2422370978581550832052537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3229827971442067776070049 2422370978581550832052537)
              ·
                refine ⟨1816778233936163124039403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2422370978581550832052537 1816778233936163124039403)
                ·
                  refine ⟨2725167350904244686059105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816778233936163124039403 2725167350904244686059105)
                  ·
                    refine ⟨2043875513178183514544329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2725167350904244686059105 2043875513178183514544329)
                    ·
                      refine ⟨1532906634883637635908247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2043875513178183514544329 1532906634883637635908247)
                      ·
                        rfl

theorem cell23_2985325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_2985325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985325 prefixEnd_2985325 := by exact prefixLift 2985325
  have htrace : WordTrace (prefixWord ++ tailWord_2985325) baseStart_2985325 baseEnd_2985325 := by
    simpa [prefixWord, tailWord_2985325, baseEnd_2985325] using wordTrace_append hprefix tailTrace_2985325
  have hstable : (prefixWord ++ tailWord_2985325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985325).length < 2 ^ (prefixWord ++ tailWord_2985325).sum := by decide
  have hdescent : baseEnd_2985325 < baseStart_2985325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985330 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_2985330 : Nat := 118140960795 + 2985330 * 2 ^ 59
def prefixEnd_2985330 : Nat := 4983230072969 + 3 ^ 40 * 2985330 * 2
def baseEnd_2985330 : Nat := 1532909202286910116345723

theorem tailTrace_2985330 : CollatzResearch.WordTrace tailWord_2985330 prefixEnd_2985330 1532909202286910116345723 := by
  unfold tailWord_2985330
  simp only [CollatzResearch.WordTrace]
  refine ⟨27220982568666684654394361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72589286849777825745051629 27220982568666684654394361)
  ·
    refine ⟨20415736926500013490795771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27220982568666684654394361 20415736926500013490795771)
    ·
      refine ⟨30623605389750020236193657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20415736926500013490795771 30623605389750020236193657)
      ·
        refine ⟨22967704042312515177145243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30623605389750020236193657 22967704042312515177145243)
        ·
          refine ⟨34451556063468772765717865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22967704042312515177145243 34451556063468772765717865)
          ·
            refine ⟨25838667047601579574288399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34451556063468772765717865 25838667047601579574288399)
            ·
              refine ⟨38758000571402369361432599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25838667047601579574288399 38758000571402369361432599)
              ·
                refine ⟨58137000857103554042148899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38758000571402369361432599 58137000857103554042148899)
                ·
                  refine ⟨87205501285655331063223349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58137000857103554042148899 87205501285655331063223349)
                  ·
                    refine ⟨8175515745530187287177189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87205501285655331063223349 8175515745530187287177189)
                    ·
                      refine ⟨1532909202286910116345723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8175515745530187287177189 1532909202286910116345723)
                      ·
                        rfl

theorem cell23_2985330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_2985330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985330 prefixEnd_2985330 := by exact prefixLift 2985330
  have htrace : WordTrace (prefixWord ++ tailWord_2985330) baseStart_2985330 baseEnd_2985330 := by
    simpa [prefixWord, tailWord_2985330, baseEnd_2985330] using wordTrace_append hprefix tailTrace_2985330
  have hstable : (prefixWord ++ tailWord_2985330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985330).length < 2 ^ (prefixWord ++ tailWord_2985330).sum := by decide
  have hdescent : baseEnd_2985330 < baseStart_2985330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985340 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 2, 6]
def baseStart_2985340 : Nat := 118140960795 + 2985340 * 2 ^ 59
def prefixEnd_2985340 : Nat := 4983230072969 + 3 ^ 40 * 2985340 * 2
def baseEnd_2985340 : Nat := 510971445697818359073559

theorem tailTrace_2985340 : CollatzResearch.WordTrace tailWord_2985340 prefixEnd_2985340 510971445697818359073559 := by
  unfold tailWord_2985340
  simp only [CollatzResearch.WordTrace]
  refine ⟨54442147502315255162720737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72589530003087006883627649 54442147502315255162720737)
  ·
    refine ⟨40831610626736441372040553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54442147502315255162720737 40831610626736441372040553)
    ·
      refine ⟨30623707970052331029030415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40831610626736441372040553 30623707970052331029030415)
      ·
        refine ⟨45935561955078496543545623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30623707970052331029030415 45935561955078496543545623)
        ·
          refine ⟨68903342932617744815318435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45935561955078496543545623 68903342932617744815318435)
          ·
            refine ⟨103355014398926617222977653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68903342932617744815318435 103355014398926617222977653)
            ·
              refine ⟨9689532599899370364654155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103355014398926617222977653 9689532599899370364654155)
              ·
                refine ⟨14534298899849055546981233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9689532599899370364654155 14534298899849055546981233)
                ·
                  refine ⟨10900724174886791660235925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14534298899849055546981233 10900724174886791660235925)
                  ·
                    refine ⟨510971445697818359073559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10900724174886791660235925 510971445697818359073559)
                    ·
                      rfl

theorem cell23_2985340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_2985340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985340 prefixEnd_2985340 := by exact prefixLift 2985340
  have htrace : WordTrace (prefixWord ++ tailWord_2985340) baseStart_2985340 baseEnd_2985340 := by
    simpa [prefixWord, tailWord_2985340, baseEnd_2985340] using wordTrace_append hprefix tailTrace_2985340
  have hstable : (prefixWord ++ tailWord_2985340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985340).length < 2 ^ (prefixWord ++ tailWord_2985340).sum := by decide
  have hdescent : baseEnd_2985340 < baseStart_2985340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985370 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 9]
def baseStart_2985370 : Nat := 118140960795 + 2985370 * 2 ^ 59
def prefixEnd_2985370 : Nat := 4983230072969 + 3 ^ 40 * 2985370 * 2
def baseEnd_2985370 : Nat := 170325526834787773316171

theorem tailTrace_2985370 : CollatzResearch.WordTrace tailWord_2985370 prefixEnd_2985370 170325526834787773316171 := by
  unfold tailWord_2985370
  simp only [CollatzResearch.WordTrace]
  refine ⟨27221347298630456362258391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72590259463014550299355709 27221347298630456362258391)
  ·
    refine ⟨40832020947945684543387587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27221347298630456362258391 40832020947945684543387587)
    ·
      refine ⟨61248031421918526815081381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40832020947945684543387587 61248031421918526815081381)
      ·
        refine ⟨11484005891609723777827759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61248031421918526815081381 11484005891609723777827759)
        ·
          refine ⟨17226008837414585666741639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11484005891609723777827759 17226008837414585666741639)
          ·
            refine ⟨25839013256121878500112459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17226008837414585666741639 25839013256121878500112459)
            ·
              refine ⟨38758519884182817750168689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25839013256121878500112459 38758519884182817750168689)
              ·
                refine ⟨29068889913137113312626517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38758519884182817750168689 29068889913137113312626517)
                ·
                  refine ⟨170325526834787773316171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29068889913137113312626517 170325526834787773316171)
                  ·
                    rfl

theorem cell23_2985370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 9].length) (baseStart_2985370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985370 prefixEnd_2985370 := by exact prefixLift 2985370
  have htrace : WordTrace (prefixWord ++ tailWord_2985370) baseStart_2985370 baseEnd_2985370 := by
    simpa [prefixWord, tailWord_2985370, baseEnd_2985370] using wordTrace_append hprefix tailTrace_2985370
  have hstable : (prefixWord ++ tailWord_2985370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985370).length < 2 ^ (prefixWord ++ tailWord_2985370).sum := by decide
  have hdescent : baseEnd_2985370 < baseStart_2985370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985400 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 1, 7]
def baseStart_2985400 : Nat := 118140960795 + 2985400 * 2 ^ 59
def prefixEnd_2985400 : Nat := 4983230072969 + 3 ^ 40 * 2985400 * 2
def baseEnd_2985400 : Nat := 510981715310908280823467

theorem tailTrace_2985400 : CollatzResearch.WordTrace tailWord_2985400 prefixEnd_2985400 510981715310908280823467 := by
  unfold tailWord_2985400
  simp only [CollatzResearch.WordTrace]
  refine ⟨54443241692206570286312827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72590988922942093715083769 54443241692206570286312827)
  ·
    refine ⟨81664862538309855429469241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54443241692206570286312827 81664862538309855429469241)
    ·
      refine ⟨61248646903732391572101931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81664862538309855429469241 61248646903732391572101931)
      ·
        refine ⟨91872970355598587358152897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61248646903732391572101931 91872970355598587358152897)
        ·
          refine ⟨68904727766698940518614673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91872970355598587358152897 68904727766698940518614673)
          ·
            refine ⟨51678545825024205388961005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68904727766698940518614673 51678545825024205388961005)
            ·
              refine ⟨19379454684384077020860377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51678545825024205388961005 19379454684384077020860377)
              ·
                refine ⟨14534591013288057765645283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19379454684384077020860377 14534591013288057765645283)
                ·
                  refine ⟨21801886519932086648467925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14534591013288057765645283 21801886519932086648467925)
                  ·
                    refine ⟨510981715310908280823467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21801886519932086648467925 510981715310908280823467)
                    ·
                      rfl

theorem cell23_2985400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_2985400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985400 prefixEnd_2985400 := by exact prefixLift 2985400
  have htrace : WordTrace (prefixWord ++ tailWord_2985400) baseStart_2985400 baseEnd_2985400 := by
    simpa [prefixWord, tailWord_2985400, baseEnd_2985400] using wordTrace_append hprefix tailTrace_2985400
  have hstable : (prefixWord ++ tailWord_2985400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985400).length < 2 ^ (prefixWord ++ tailWord_2985400).sum := by decide
  have hdescent : baseEnd_2985400 < baseStart_2985400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985407 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 2, 5, 2]
def baseStart_2985407 : Nat := 118140960795 + 2985407 * 2 ^ 59
def prefixEnd_2985407 : Nat := 4983230072969 + 3 ^ 40 * 2985407 * 2
def baseEnd_2985407 : Nat := 1532948740297306315082869

theorem tailTrace_2985407 : CollatzResearch.WordTrace tailWord_2985407 prefixEnd_2985407 1532948740297306315082869 := by
  unfold tailWord_2985407
  simp only [CollatzResearch.WordTrace]
  refine ⟨108886738695387780768130475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72591159130258520512086983 108886738695387780768130475)
  ·
    refine ⟨163330108043081671152195713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108886738695387780768130475 163330108043081671152195713)
    ·
      refine ⟨122497581032311253364146785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163330108043081671152195713 122497581032311253364146785)
      ·
        refine ⟨91873185774233440023110089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122497581032311253364146785 91873185774233440023110089)
        ·
          refine ⟨68904889330675080017332567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91873185774233440023110089 68904889330675080017332567)
          ·
            refine ⟨103357333996012620025998851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68904889330675080017332567 103357333996012620025998851)
            ·
              refine ⟨155036000994018930038998277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103357333996012620025998851 155036000994018930038998277)
              ·
                refine ⟨29069250186378549382312177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155036000994018930038998277 29069250186378549382312177)
                ·
                  refine ⟨21801937639783912036734133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29069250186378549382312177 21801937639783912036734133)
                  ·
                    refine ⟨2043931653729741753443825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21801937639783912036734133 2043931653729741753443825)
                    ·
                      refine ⟨1532948740297306315082869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2043931653729741753443825 1532948740297306315082869)
                      ·
                        rfl

theorem cell23_2985407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 5, 2].length) (baseStart_2985407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985407 prefixEnd_2985407 := by exact prefixLift 2985407
  have htrace : WordTrace (prefixWord ++ tailWord_2985407) baseStart_2985407 baseEnd_2985407 := by
    simpa [prefixWord, tailWord_2985407, baseEnd_2985407] using wordTrace_append hprefix tailTrace_2985407
  have hstable : (prefixWord ++ tailWord_2985407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985407).length < 2 ^ (prefixWord ++ tailWord_2985407).sum := by decide
  have hdescent : baseEnd_2985407 < baseStart_2985407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985440 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 5]
def baseStart_2985440 : Nat := 118140960795 + 2985440 * 2 ^ 59
def prefixEnd_2985440 : Nat := 4983230072969 + 3 ^ 40 * 2985440 * 2
def baseEnd_2985440 : Nat := 1532965685158904685970217

theorem tailTrace_2985440 : CollatzResearch.WordTrace tailWord_2985440 prefixEnd_2985440 1532965685158904685970217 := by
  unfold tailWord_2985440
  simp only [CollatzResearch.WordTrace]
  refine ⟨54443971152134113702040887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72591961536178818269387849 54443971152134113702040887)
  ·
    refine ⟨81665956728201170553061331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54443971152134113702040887 81665956728201170553061331)
    ·
      refine ⟨122498935092301755829591997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81665956728201170553061331 122498935092301755829591997)
      ·
        refine ⟨45937100659613158436096999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122498935092301755829591997 45937100659613158436096999)
        ·
          refine ⟨68905650989419737654145499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45937100659613158436096999 68905650989419737654145499)
          ·
            refine ⟨103358476484129606481218249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68905650989419737654145499 103358476484129606481218249)
            ·
              refine ⟨77518857363097204860913687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103358476484129606481218249 77518857363097204860913687)
              ·
                refine ⟨116278286044645807291370531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77518857363097204860913687 116278286044645807291370531)
                ·
                  refine ⟨174417429066968710937055797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116278286044645807291370531 174417429066968710937055797)
                  ·
                    refine ⟨16351633975028316650348981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 174417429066968710937055797 16351633975028316650348981)
                    ·
                      refine ⟨1532965685158904685970217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16351633975028316650348981 1532965685158904685970217)
                      ·
                        rfl

theorem cell23_2985440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_2985440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985440 prefixEnd_2985440 := by exact prefixLift 2985440
  have htrace : WordTrace (prefixWord ++ tailWord_2985440) baseStart_2985440 baseEnd_2985440 := by
    simpa [prefixWord, tailWord_2985440, baseEnd_2985440] using wordTrace_append hprefix tailTrace_2985440
  have hstable : (prefixWord ++ tailWord_2985440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985440).length < 2 ^ (prefixWord ++ tailWord_2985440).sum := by decide
  have hdescent : baseEnd_2985440 < baseStart_2985440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985454 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 1, 6, 2]
def baseStart_2985454 : Nat := 118140960795 + 2985454 * 2 ^ 59
def prefixEnd_2985454 : Nat := 4983230072969 + 3 ^ 40 * 2985454 * 2
def baseEnd_2985454 : Nat := 1532972873888067631195153

theorem tailTrace_2985454 : CollatzResearch.WordTrace tailWord_2985454 prefixEnd_2985454 1532972873888067631195153 := by
  unfold tailWord_2985454
  simp only [CollatzResearch.WordTrace]
  refine ⟨13611056615777188474386427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72592301950811671863394277 13611056615777188474386427)
  ·
    refine ⟨20416584923665782711579641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13611056615777188474386427 20416584923665782711579641)
    ·
      refine ⟨15312438692749337033684731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20416584923665782711579641 15312438692749337033684731)
      ·
        refine ⟨22968658039124005550527097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15312438692749337033684731 22968658039124005550527097)
        ·
          refine ⟨17226493529343004162895323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22968658039124005550527097 17226493529343004162895323)
          ·
            refine ⟨25839740294014506244342985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17226493529343004162895323 25839740294014506244342985)
            ·
              refine ⟨19379805220510879683257239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25839740294014506244342985 19379805220510879683257239)
              ·
                refine ⟨29069707830766319524885859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19379805220510879683257239 29069707830766319524885859)
                ·
                  refine ⟨43604561746149479287328789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29069707830766319524885859 43604561746149479287328789)
                  ·
                    refine ⟨2043963831850756841593537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43604561746149479287328789 2043963831850756841593537)
                    ·
                      refine ⟨1532972873888067631195153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2043963831850756841593537 1532972873888067631195153)
                      ·
                        rfl

theorem cell23_2985454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_2985454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985454 prefixEnd_2985454 := by exact prefixLift 2985454
  have htrace : WordTrace (prefixWord ++ tailWord_2985454) baseStart_2985454 baseEnd_2985454 := by
    simpa [prefixWord, tailWord_2985454, baseEnd_2985454] using wordTrace_append hprefix tailTrace_2985454
  have hstable : (prefixWord ++ tailWord_2985454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985454).length < 2 ^ (prefixWord ++ tailWord_2985454).sum := by decide
  have hdescent : baseEnd_2985454 < baseStart_2985454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985547 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 5]
def baseStart_2985547 : Nat := 118140960795 + 2985547 * 2 ^ 59
def prefixEnd_2985547 : Nat := 4983230072969 + 3 ^ 40 * 2985547 * 2
def baseEnd_2985547 : Nat := 1533020627588935767332225

theorem tailTrace_2985547 : CollatzResearch.WordTrace tailWord_2985547 prefixEnd_2985547 1533020627588935767332225 := by
  unfold tailWord_2985547
  simp only [CollatzResearch.WordTrace]
  refine ⟨108891844914880584678226895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72594563276587056452151263 108891844914880584678226895)
  ·
    refine ⟨163337767372320877017340343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108891844914880584678226895 163337767372320877017340343)
    ·
      refine ⟨245006651058481315526010515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163337767372320877017340343 245006651058481315526010515)
      ·
        refine ⟨367509976587721973289015773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245006651058481315526010515 367509976587721973289015773)
        ·
          refine ⟨137816241220395739983380915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367509976587721973289015773 137816241220395739983380915)
          ·
            refine ⟨206724361830593609975071373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137816241220395739983380915 206724361830593609975071373)
            ·
              refine ⟨77521635686472603740651765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206724361830593609975071373 77521635686472603740651765)
              ·
                refine ⟨7267653345606806600686103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77521635686472603740651765 7267653345606806600686103)
                ·
                  refine ⟨10901480018410209901029155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7267653345606806600686103 10901480018410209901029155)
                  ·
                    refine ⟨16352220027615314851543733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10901480018410209901029155 16352220027615314851543733)
                    ·
                      refine ⟨1533020627588935767332225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16352220027615314851543733 1533020627588935767332225)
                      ·
                        rfl

theorem cell23_2985547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 5].length) (baseStart_2985547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985547 prefixEnd_2985547 := by exact prefixLift 2985547
  have htrace : WordTrace (prefixWord ++ tailWord_2985547) baseStart_2985547 baseEnd_2985547 := by
    simpa [prefixWord, tailWord_2985547, baseEnd_2985547] using wordTrace_append hprefix tailTrace_2985547
  have hstable : (prefixWord ++ tailWord_2985547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985547).length < 2 ^ (prefixWord ++ tailWord_2985547).sum := by decide
  have hdescent : baseEnd_2985547 < baseStart_2985547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985557 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_2985557 : Nat := 118140960795 + 2985557 * 2 ^ 59
def prefixEnd_2985557 : Nat := 4983230072969 + 3 ^ 40 * 2985557 * 2
def baseEnd_2985557 : Nat := 1533025762395480728207179

theorem tailTrace_2985557 : CollatzResearch.WordTrace tailWord_2985557 prefixEnd_2985557 1533025762395480728207179 := by
  unfold tailWord_2985557
  simp only [CollatzResearch.WordTrace]
  refine ⟨108892209644844356386090925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72594806429896237590727283 108892209644844356386090925)
  ·
    refine ⟨40834578616816633644784097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108892209644844356386090925 40834578616816633644784097)
    ·
      refine ⟨30625933962612475233588073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40834578616816633644784097 30625933962612475233588073)
      ·
        refine ⟨22969450471959356425191055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30625933962612475233588073 22969450471959356425191055)
        ·
          refine ⟨34454175707939034637786583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22969450471959356425191055 34454175707939034637786583)
          ·
            refine ⟨51681263561908551956679875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34454175707939034637786583 51681263561908551956679875)
            ·
              refine ⟨77521895342862827935019813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51681263561908551956679875 77521895342862827935019813)
              ·
                refine ⟨14535355376786780237816215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77521895342862827935019813 14535355376786780237816215)
                ·
                  refine ⟨21803033065180170356724323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14535355376786780237816215 21803033065180170356724323)
                  ·
                    refine ⟨32704549597770255535086485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21803033065180170356724323 32704549597770255535086485)
                    ·
                      refine ⟨1533025762395480728207179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32704549597770255535086485 1533025762395480728207179)
                      ·
                        rfl

theorem cell23_2985557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_2985557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985557 prefixEnd_2985557 := by exact prefixLift 2985557
  have htrace : WordTrace (prefixWord ++ tailWord_2985557) baseStart_2985557 baseEnd_2985557 := by
    simpa [prefixWord, tailWord_2985557, baseEnd_2985557] using wordTrace_append hprefix tailTrace_2985557
  have hstable : (prefixWord ++ tailWord_2985557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985557).length < 2 ^ (prefixWord ++ tailWord_2985557).sum := by decide
  have hdescent : baseEnd_2985557 < baseStart_2985557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985564 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2985564 : Nat := 118140960795 + 2985564 * 2 ^ 59
def prefixEnd_2985564 : Nat := 4983230072969 + 3 ^ 40 * 2985564 * 2
def baseEnd_2985564 : Nat := 1533029356760062200819647

theorem tailTrace_2985564 : CollatzResearch.WordTrace tailWord_2985564 prefixEnd_2985564 1533029356760062200819647 := by
  unfold tailWord_2985564
  simp only [CollatzResearch.WordTrace]
  refine ⟨54446232477909498290797873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72594976637212664387730497 54446232477909498290797873)
  ·
    refine ⟨40834674358432123718098405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54446232477909498290797873 40834674358432123718098405)
    ·
      refine ⟨7656501442206023197143451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40834674358432123718098405 7656501442206023197143451)
      ·
        refine ⟨11484752163309034795715177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7656501442206023197143451 11484752163309034795715177)
        ·
          refine ⟨8613564122481776096786383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11484752163309034795715177 8613564122481776096786383)
          ·
            refine ⟨12920346183722664145179575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8613564122481776096786383 12920346183722664145179575)
            ·
              refine ⟨19380519275583996217769363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12920346183722664145179575 19380519275583996217769363)
              ·
                refine ⟨29070778913375994326654045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19380519275583996217769363 29070778913375994326654045)
                ·
                  refine ⟨10901542092515997872495267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29070778913375994326654045 10901542092515997872495267)
                  ·
                    refine ⟨16352313138773996808742901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10901542092515997872495267 16352313138773996808742901)
                    ·
                      refine ⟨1533029356760062200819647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16352313138773996808742901 1533029356760062200819647)
                      ·
                        rfl

theorem cell23_2985564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2985564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985564 prefixEnd_2985564 := by exact prefixLift 2985564
  have htrace : WordTrace (prefixWord ++ tailWord_2985564) baseStart_2985564 baseEnd_2985564 := by
    simpa [prefixWord, tailWord_2985564, baseEnd_2985564] using wordTrace_append hprefix tailTrace_2985564
  have hstable : (prefixWord ++ tailWord_2985564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985564).length < 2 ^ (prefixWord ++ tailWord_2985564).sum := by decide
  have hdescent : baseEnd_2985564 < baseStart_2985564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985578 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 3, 2, 2]
def baseStart_2985578 : Nat := 118140960795 + 2985578 * 2 ^ 59
def prefixEnd_2985578 : Nat := 4983230072969 + 3 ^ 40 * 2985578 * 2
def baseEnd_2985578 : Nat := 1533036545489225146044583

theorem tailTrace_2985578 : CollatzResearch.WordTrace tailWord_2985578 prefixEnd_2985578 1533036545489225146044583 := by
  unfold tailWord_2985578
  simp only [CollatzResearch.WordTrace]
  refine ⟨27223243894442069243151347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72595317051845517981736925 27223243894442069243151347)
  ·
    refine ⟨40834865841663103864727021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27223243894442069243151347 40834865841663103864727021)
    ·
      refine ⟨15313074690623663949272633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40834865841663103864727021 15313074690623663949272633)
      ·
        refine ⟨11484806017967747961954475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15313074690623663949272633 11484806017967747961954475)
        ·
          refine ⟨17227209026951621942931713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11484806017967747961954475 17227209026951621942931713)
          ·
            refine ⟨12920406770213716457198785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17227209026951621942931713 12920406770213716457198785)
            ·
              refine ⟨9690305077660287342899089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12920406770213716457198785 9690305077660287342899089)
              ·
                refine ⟨7267728808245215507174317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9690305077660287342899089 7267728808245215507174317)
                ·
                  refine ⟨2725398303091955815190369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7267728808245215507174317 2725398303091955815190369)
                  ·
                    refine ⟨2044048727318966861392777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2725398303091955815190369 2044048727318966861392777)
                    ·
                      refine ⟨1533036545489225146044583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2044048727318966861392777 1533036545489225146044583)
                      ·
                        rfl

theorem cell23_2985578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_2985578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985578 prefixEnd_2985578 := by exact prefixLift 2985578
  have htrace : WordTrace (prefixWord ++ tailWord_2985578) baseStart_2985578 baseEnd_2985578 := by
    simpa [prefixWord, tailWord_2985578, baseEnd_2985578] using wordTrace_append hprefix tailTrace_2985578
  have hstable : (prefixWord ++ tailWord_2985578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985578).length < 2 ^ (prefixWord ++ tailWord_2985578).sum := by decide
  have hdescent : baseEnd_2985578 < baseStart_2985578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985584 : List Nat := [2, 1, 1, 1, 6, 1, 4, 7]
def baseStart_2985584 : Nat := 118140960795 + 2985584 * 2 ^ 59
def prefixEnd_2985584 : Nat := 4983230072969 + 3 ^ 40 * 2985584 * 2
def baseEnd_2985584 : Nat := 56779245421227856391465

theorem tailTrace_2985584 : CollatzResearch.WordTrace tailWord_2985584 prefixEnd_2985584 56779245421227856391465 := by
  unfold tailWord_2985584
  simp only [CollatzResearch.WordTrace]
  refine ⟨54446597207873269998661903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72595462943831026664882537 54446597207873269998661903)
  ·
    refine ⟨81669895811809904997992855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54446597207873269998661903 81669895811809904997992855)
    ·
      refine ⟨122504843717714857496989283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81669895811809904997992855 122504843717714857496989283)
      ·
        refine ⟨183757265576572286245483925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122504843717714857496989283 183757265576572286245483925)
        ·
          refine ⟨8613621823901825917757059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 183757265576572286245483925 8613621823901825917757059)
          ·
            refine ⟨12920432735852738876635589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8613621823901825917757059 12920432735852738876635589)
            ·
              refine ⟨2422581137972388539369173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12920432735852738876635589 2422581137972388539369173)
              ·
                refine ⟨56779245421227856391465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2422581137972388539369173 56779245421227856391465)
                ·
                  rfl

theorem cell23_2985584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 7].length) (baseStart_2985584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985584 prefixEnd_2985584 := by exact prefixLift 2985584
  have htrace : WordTrace (prefixWord ++ tailWord_2985584) baseStart_2985584 baseEnd_2985584 := by
    simpa [prefixWord, tailWord_2985584, baseEnd_2985584] using wordTrace_append hprefix tailTrace_2985584
  have hstable : (prefixWord ++ tailWord_2985584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985584).length < 2 ^ (prefixWord ++ tailWord_2985584).sum := by decide
  have hdescent : baseEnd_2985584 < baseStart_2985584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985611 : List Nat := [1, 1, 1, 1, 4, 1, 4, 4, 2, 1, 3]
def baseStart_2985611 : Nat := 118140960795 + 2985611 * 2 ^ 59
def prefixEnd_2985611 : Nat := 4983230072969 + 3 ^ 40 * 2985611 * 2
def baseEnd_2985611 : Nat := 1533053490350823516931931

theorem tailTrace_2985611 : CollatzResearch.WordTrace tailWord_2985611 prefixEnd_2985611 1533053490350823516931931 := by
  unfold tailWord_2985611
  simp only [CollatzResearch.WordTrace]
  refine ⟨108894179186648723608556687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72596119457765815739037791 108894179186648723608556687)
  ·
    refine ⟨163341268779973085412835031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108894179186648723608556687 163341268779973085412835031)
    ·
      refine ⟨245011903169959628119252547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163341268779973085412835031 245011903169959628119252547)
      ·
        refine ⟨367517854754939442178878821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245011903169959628119252547 367517854754939442178878821)
        ·
          refine ⟨68909597766551145408539779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 367517854754939442178878821 68909597766551145408539779)
          ·
            refine ⟨103364396649826718112809669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68909597766551145408539779 103364396649826718112809669)
            ·
              refine ⟨19380824371842509646151813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103364396649826718112809669 19380824371842509646151813)
              ·
                refine ⟨3633904569720470558653465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19380824371842509646151813 3633904569720470558653465)
                ·
                  refine ⟨2725428427290352918990099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3633904569720470558653465 2725428427290352918990099)
                  ·
                    refine ⟨4088142640935529378485149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2725428427290352918990099 4088142640935529378485149)
                    ·
                      refine ⟨1533053490350823516931931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4088142640935529378485149 1533053490350823516931931)
                      ·
                        rfl

theorem cell23_2985611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 1, 3].length) (baseStart_2985611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985611 prefixEnd_2985611 := by exact prefixLift 2985611
  have htrace : WordTrace (prefixWord ++ tailWord_2985611) baseStart_2985611 baseEnd_2985611 := by
    simpa [prefixWord, tailWord_2985611, baseEnd_2985611] using wordTrace_append hprefix tailTrace_2985611
  have hstable : (prefixWord ++ tailWord_2985611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985611).length < 2 ^ (prefixWord ++ tailWord_2985611).sum := by decide
  have hdescent : baseEnd_2985611 < baseStart_2985611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985651 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 1, 4, 2]
def baseStart_2985651 : Nat := 118140960795 + 2985651 * 2 ^ 59
def prefixEnd_2985651 : Nat := 4983230072969 + 3 ^ 40 * 2985651 * 2
def baseEnd_2985651 : Nat := 1533074029577003360431747

theorem tailTrace_2985651 : CollatzResearch.WordTrace tailWord_2985651 prefixEnd_2985651 1533074029577003360431747 := by
  unfold tailWord_2985651
  simp only [CollatzResearch.WordTrace]
  refine ⟨108895638106503810440012807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72597092071002540293341871 108895638106503810440012807)
  ·
    refine ⟨163343457159755715660019211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108895638106503810440012807 163343457159755715660019211)
    ·
      refine ⟨245015185739633573490028817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163343457159755715660019211 245015185739633573490028817)
      ·
        refine ⟨183761389304725180117521613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245015185739633573490028817 183761389304725180117521613)
        ·
          refine ⟨68910520989271942544070605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183761389304725180117521613 68910520989271942544070605)
          ·
            refine ⟨25841445370976978454026477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68910520989271942544070605 25841445370976978454026477)
            ·
              refine ⟨9690542014116366920259929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25841445370976978454026477 9690542014116366920259929)
              ·
                refine ⟨7267906510587275190194947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9690542014116366920259929 7267906510587275190194947)
                ·
                  refine ⟨10901859765880912785292421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7267906510587275190194947 10901859765880912785292421)
                  ·
                    refine ⟨2044098706102671147242329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10901859765880912785292421 2044098706102671147242329)
                    ·
                      refine ⟨1533074029577003360431747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2044098706102671147242329 1533074029577003360431747)
                      ·
                        rfl

theorem cell23_2985651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 4, 2].length) (baseStart_2985651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985651 prefixEnd_2985651 := by exact prefixLift 2985651
  have htrace : WordTrace (prefixWord ++ tailWord_2985651) baseStart_2985651 baseEnd_2985651 := by
    simpa [prefixWord, tailWord_2985651, baseEnd_2985651] using wordTrace_append hprefix tailTrace_2985651
  have hstable : (prefixWord ++ tailWord_2985651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985651).length < 2 ^ (prefixWord ++ tailWord_2985651).sum := by decide
  have hdescent : baseEnd_2985651 < baseStart_2985651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985655 : List Nat := [1, 1, 3, 1, 5, 2, 3, 1, 1, 3, 2]
def baseStart_2985655 : Nat := 118140960795 + 2985655 * 2 ^ 59
def prefixEnd_2985655 : Nat := 4983230072969 + 3 ^ 40 * 2985655 * 2
def baseEnd_2985655 : Nat := 1533076083499621344781729

theorem tailTrace_2985655 : CollatzResearch.WordTrace tailWord_2985655 prefixEnd_2985655 1533076083499621344781729 := by
  unfold tailWord_2985655
  simp only [CollatzResearch.WordTrace]
  refine ⟨108895783998489319123158419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72597189332326212748772279 108895783998489319123158419)
  ·
    refine ⟨163343675997733978684737629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108895783998489319123158419 163343675997733978684737629)
    ·
      refine ⟨61253878499150242006776611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163343675997733978684737629 61253878499150242006776611)
      ·
        refine ⟨91880817748725363010164917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61253878499150242006776611 91880817748725363010164917)
        ·
          refine ⟨8613826663943002782202961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91880817748725363010164917 8613826663943002782202961)
          ·
            refine ⟨6460369997957252086652221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8613826663943002782202961 6460369997957252086652221)
            ·
              refine ⟨2422638749233969532494583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6460369997957252086652221 2422638749233969532494583)
              ·
                refine ⟨3633958123850954298741875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2422638749233969532494583 3633958123850954298741875)
                ·
                  refine ⟨5450937185776431448112813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3633958123850954298741875 5450937185776431448112813)
                  ·
                    refine ⟨2044101444666161793042305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5450937185776431448112813 2044101444666161793042305)
                    ·
                      refine ⟨1533076083499621344781729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2044101444666161793042305 1533076083499621344781729)
                      ·
                        rfl

theorem cell23_2985655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 1, 3, 2].length) (baseStart_2985655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985655 prefixEnd_2985655 := by exact prefixLift 2985655
  have htrace : WordTrace (prefixWord ++ tailWord_2985655) baseStart_2985655 baseEnd_2985655 := by
    simpa [prefixWord, tailWord_2985655, baseEnd_2985655] using wordTrace_append hprefix tailTrace_2985655
  have hstable : (prefixWord ++ tailWord_2985655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985655).length < 2 ^ (prefixWord ++ tailWord_2985655).sum := by decide
  have hdescent : baseEnd_2985655 < baseStart_2985655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985664 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 4]
def baseStart_2985664 : Nat := 118140960795 + 2985664 * 2 ^ 59
def prefixEnd_2985664 : Nat := 4983230072969 + 3 ^ 40 * 2985664 * 2
def baseEnd_2985664 : Nat := 1533080704825511809569187

theorem tailTrace_2985664 : CollatzResearch.WordTrace tailWord_2985664 prefixEnd_2985664 1533080704825511809569187 := by
  unfold tailWord_2985664
  simp only [CollatzResearch.WordTrace]
  refine ⟨54448056127728356830118023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72597408170304475773490697 54448056127728356830118023)
  ·
    refine ⟨81672084191592535245177035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54448056127728356830118023 81672084191592535245177035)
    ·
      refine ⟨122508126287388802867765553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81672084191592535245177035 122508126287388802867765553)
      ·
        refine ⟨91881094715541602150824165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122508126287388802867765553 91881094715541602150824165)
        ·
          refine ⟨17227705259164050403279531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91881094715541602150824165 17227705259164050403279531)
          ·
            refine ⟨25841557888746075604919297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17227705259164050403279531 25841557888746075604919297)
            ·
              refine ⟨19381168416559556703689473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25841557888746075604919297 19381168416559556703689473)
              ·
                refine ⟨14535876312419667527767105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19381168416559556703689473 14535876312419667527767105)
                ·
                  refine ⟨10901907234314750645825329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14535876312419667527767105 10901907234314750645825329)
                  ·
                    refine ⟨8176430425736062984368997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10901907234314750645825329 8176430425736062984368997)
                    ·
                      refine ⟨1533080704825511809569187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8176430425736062984368997 1533080704825511809569187)
                      ·
                        rfl

theorem cell23_2985664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_2985664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985664 prefixEnd_2985664 := by exact prefixLift 2985664
  have htrace : WordTrace (prefixWord ++ tailWord_2985664) baseStart_2985664 baseEnd_2985664 := by
    simpa [prefixWord, tailWord_2985664, baseEnd_2985664] using wordTrace_append hprefix tailTrace_2985664
  have hstable : (prefixWord ++ tailWord_2985664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985664).length < 2 ^ (prefixWord ++ tailWord_2985664).sum := by decide
  have hdescent : baseEnd_2985664 < baseStart_2985664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985761 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 1, 4, 3]
def baseStart_2985761 : Nat := 118140960795 + 2985761 * 2 ^ 59
def prefixEnd_2985761 : Nat := 4983230072969 + 3 ^ 40 * 2985761 * 2
def baseEnd_2985761 : Nat := 1533130512448997930056241

theorem tailTrace_2985761 : CollatzResearch.WordTrace tailWord_2985761 prefixEnd_2985761 1533130512448997930056241 := by
  unfold tailWord_2985761
  simp only [CollatzResearch.WordTrace]
  refine ⟨108899650136105299226517137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72599766757403532817678091 108899650136105299226517137)
  ·
    refine ⟨81674737602078974419887853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108899650136105299226517137 81674737602078974419887853)
    ·
      refine ⟨30628026600779615407457945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81674737602078974419887853 30628026600779615407457945)
      ·
        refine ⟨22971019950584711555593459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30628026600779615407457945 22971019950584711555593459)
        ·
          refine ⟨34456529925877067333390189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22971019950584711555593459 34456529925877067333390189)
          ·
            refine ⟨12921198722203900250021321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34456529925877067333390189 12921198722203900250021321)
            ·
              refine ⟨9690899041652925187515991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12921198722203900250021321 9690899041652925187515991)
              ·
                refine ⟨14536348562479387781273987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9690899041652925187515991 14536348562479387781273987)
                ·
                  refine ⟨21804522843719081671910981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14536348562479387781273987 21804522843719081671910981)
                  ·
                    refine ⟨4088348033197327813483309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21804522843719081671910981 4088348033197327813483309)
                    ·
                      refine ⟨1533130512448997930056241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4088348033197327813483309 1533130512448997930056241)
                      ·
                        rfl

theorem cell23_2985761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_2985761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985761 prefixEnd_2985761 := by exact prefixLift 2985761
  have htrace : WordTrace (prefixWord ++ tailWord_2985761) baseStart_2985761 baseEnd_2985761 := by
    simpa [prefixWord, tailWord_2985761, baseEnd_2985761] using wordTrace_append hprefix tailTrace_2985761
  have hstable : (prefixWord ++ tailWord_2985761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985761).length < 2 ^ (prefixWord ++ tailWord_2985761).sum := by decide
  have hdescent : baseEnd_2985761 < baseStart_2985761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985778 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3]
def baseStart_2985778 : Nat := 118140960795 + 2985778 * 2 ^ 59
def prefixEnd_2985778 : Nat := 4983230072969 + 3 ^ 40 * 2985778 * 2
def baseEnd_2985778 : Nat := 1533139241620124363543663

theorem tailTrace_2985778 : CollatzResearch.WordTrace tailWord_2985778 prefixEnd_2985778 1533139241620124363543663 := by
  unfold tailWord_2985778
  simp only [CollatzResearch.WordTrace]
  refine ⟨27225067544260927782471497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72600180118029140753257325 27225067544260927782471497)
  ·
    refine ⟨20418800658195695836853623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27225067544260927782471497 20418800658195695836853623)
    ·
      refine ⟨30628200987293543755280435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20418800658195695836853623 30628200987293543755280435)
      ·
        refine ⟨45942301480940315632920653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30628200987293543755280435 45942301480940315632920653)
        ·
          refine ⟨17228363055352618362345245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45942301480940315632920653 17228363055352618362345245)
          ·
            refine ⟨6460636145757231885879467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17228363055352618362345245 6460636145757231885879467)
            ·
              refine ⟨9690954218635847828819201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6460636145757231885879467 9690954218635847828819201)
              ·
                refine ⟨7268215663976885871614401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9690954218635847828819201 7268215663976885871614401)
                ·
                  refine ⟨5451161747982664403710801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7268215663976885871614401 5451161747982664403710801)
                  ·
                    refine ⟨4088371310986998302783101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5451161747982664403710801 4088371310986998302783101)
                    ·
                      refine ⟨1533139241620124363543663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4088371310986998302783101 1533139241620124363543663)
                      ·
                        rfl

theorem cell23_2985778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_2985778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985778 prefixEnd_2985778 := by exact prefixLift 2985778
  have htrace : WordTrace (prefixWord ++ tailWord_2985778) baseStart_2985778 baseEnd_2985778 := by
    simpa [prefixWord, tailWord_2985778, baseEnd_2985778] using wordTrace_append hprefix tailTrace_2985778
  have hstable : (prefixWord ++ tailWord_2985778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985778).length < 2 ^ (prefixWord ++ tailWord_2985778).sum := by decide
  have hdescent : baseEnd_2985778 < baseStart_2985778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985825 : List Nat := [1, 2, 3, 1, 1, 1, 4, 5, 1, 1, 3]
def baseStart_2985825 : Nat := 118140960795 + 2985825 * 2 ^ 59
def prefixEnd_2985825 : Nat := 4983230072969 + 3 ^ 40 * 2985825 * 2
def baseEnd_2985825 : Nat := 1533163375210885679655947

theorem tailTrace_2985825 : CollatzResearch.WordTrace tailWord_2985825 prefixEnd_2985825 1533163375210885679655947 := by
  unfold tailWord_2985825
  simp only [CollatzResearch.WordTrace]
  refine ⟨108901984407873438156846929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72601322938582292104564619 108901984407873438156846929)
  ·
    refine ⟨81676488305905078617635197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108901984407873438156846929 81676488305905078617635197)
    ·
      refine ⟨30628683114714404481613199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81676488305905078617635197 30628683114714404481613199)
      ·
        refine ⟨45943024672071606722419799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30628683114714404481613199 45943024672071606722419799)
        ·
          refine ⟨68914537008107410083629699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45943024672071606722419799 68914537008107410083629699)
          ·
            refine ⟨103371805512161115125444549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68914537008107410083629699 103371805512161115125444549)
            ·
              refine ⟨19382213533530209086020853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103371805512161115125444549 19382213533530209086020853)
              ·
                refine ⟨1817082518768457101814455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19382213533530209086020853 1817082518768457101814455)
                ·
                  refine ⟨2725623778152685652721683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817082518768457101814455 2725623778152685652721683)
                  ·
                    refine ⟨4088435667229028479082525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2725623778152685652721683 4088435667229028479082525)
                    ·
                      refine ⟨1533163375210885679655947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4088435667229028479082525 1533163375210885679655947)
                      ·
                        rfl

theorem cell23_2985825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_2985825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985825 prefixEnd_2985825 := by exact prefixLift 2985825
  have htrace : WordTrace (prefixWord ++ tailWord_2985825) baseStart_2985825 baseEnd_2985825 := by
    simpa [prefixWord, tailWord_2985825, baseEnd_2985825] using wordTrace_append hprefix tailTrace_2985825
  have hstable : (prefixWord ++ tailWord_2985825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985825).length < 2 ^ (prefixWord ++ tailWord_2985825).sum := by decide
  have hdescent : baseEnd_2985825 < baseStart_2985825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985865 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 3, 2, 2]
def baseStart_2985865 : Nat := 118140960795 + 2985865 * 2 ^ 59
def prefixEnd_2985865 : Nat := 4983230072969 + 3 ^ 40 * 2985865 * 2
def baseEnd_2985865 : Nat := 1533183914437065523155763

theorem tailTrace_2985865 : CollatzResearch.WordTrace tailWord_2985865 prefixEnd_2985865 1533183914437065523155763 := by
  unfold tailWord_2985865
  simp only [CollatzResearch.WordTrace]
  refine ⟨108903443327728524988303049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72602295551819016658868699 108903443327728524988303049)
  ·
    refine ⟨81677582495796393741227287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108903443327728524988303049 81677582495796393741227287)
    ·
      refine ⟨122516373743694590611840931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81677582495796393741227287 122516373743694590611840931)
      ·
        refine ⟨183774560615541885917761397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122516373743694590611840931 183774560615541885917761397)
        ·
          refine ⟨17228865057707051804790131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183774560615541885917761397 17228865057707051804790131)
          ·
            refine ⟨25843297586560577707185197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17228865057707051804790131 25843297586560577707185197)
            ·
              refine ⟨9691236594960216640194449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25843297586560577707185197 9691236594960216640194449)
              ·
                refine ⟨7268427446220162480145837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9691236594960216640194449 7268427446220162480145837)
                ·
                  refine ⟨2725660292332560930054689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7268427446220162480145837 2725660292332560930054689)
                  ·
                    refine ⟨2044245219249420697541017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2725660292332560930054689 2044245219249420697541017)
                    ·
                      refine ⟨1533183914437065523155763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2044245219249420697541017 1533183914437065523155763)
                      ·
                        rfl

theorem cell23_2985865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 2, 2].length) (baseStart_2985865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985865 prefixEnd_2985865 := by exact prefixLift 2985865
  have htrace : WordTrace (prefixWord ++ tailWord_2985865) baseStart_2985865 baseEnd_2985865 := by
    simpa [prefixWord, tailWord_2985865, baseEnd_2985865] using wordTrace_append hprefix tailTrace_2985865
  have hstable : (prefixWord ++ tailWord_2985865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985865).length < 2 ^ (prefixWord ++ tailWord_2985865).sum := by decide
  have hdescent : baseEnd_2985865 < baseStart_2985865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985868 : List Nat := [2, 2, 1, 2, 1, 2, 1, 6, 1, 2, 3]
def baseStart_2985868 : Nat := 118140960795 + 2985868 * 2 ^ 59
def prefixEnd_2985868 : Nat := 4983230072969 + 3 ^ 40 * 2985868 * 2
def baseEnd_2985868 : Nat := 1533185454879029011418249

theorem tailTrace_2985868 : CollatzResearch.WordTrace tailWord_2985868 prefixEnd_2985868 1533185454879029011418249 := by
  unfold tailWord_2985868
  simp only [CollatzResearch.WordTrace]
  refine ⟨54451776373358828250331129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72602368497811771000441505 54451776373358828250331129)
  ·
    refine ⟨40838832280019121187748347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54451776373358828250331129 40838832280019121187748347)
    ·
      refine ⟨61258248420028681781622521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40838832280019121187748347 61258248420028681781622521)
      ·
        refine ⟨45943686315021511336216891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61258248420028681781622521 45943686315021511336216891)
        ·
          refine ⟨68915529472532267004325337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45943686315021511336216891 68915529472532267004325337)
          ·
            refine ⟨51686647104399200253244003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68915529472532267004325337 51686647104399200253244003)
            ·
              refine ⟨77529970656598800379866005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51686647104399200253244003 77529970656598800379866005)
              ·
                refine ⟨3634217374528068767806219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77529970656598800379866005 3634217374528068767806219)
                ·
                  refine ⟨5451326061792103151709329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3634217374528068767806219 5451326061792103151709329)
                  ·
                    refine ⟨4088494546344077363781997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5451326061792103151709329 4088494546344077363781997)
                    ·
                      refine ⟨1533185454879029011418249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4088494546344077363781997 1533185454879029011418249)
                      ·
                        rfl

theorem cell23_2985868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_2985868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985868 prefixEnd_2985868 := by exact prefixLift 2985868
  have htrace : WordTrace (prefixWord ++ tailWord_2985868) baseStart_2985868 baseEnd_2985868 := by
    simpa [prefixWord, tailWord_2985868, baseEnd_2985868] using wordTrace_append hprefix tailTrace_2985868
  have hstable : (prefixWord ++ tailWord_2985868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985868).length < 2 ^ (prefixWord ++ tailWord_2985868).sum := by decide
  have hdescent : baseEnd_2985868 < baseStart_2985868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985882 : List Nat := [3, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4]
def baseStart_2985882 : Nat := 118140960795 + 2985882 * 2 ^ 59
def prefixEnd_2985882 : Nat := 4983230072969 + 3 ^ 40 * 2985882 * 2
def baseEnd_2985882 : Nat := 1533192643608191956643185

theorem tailTrace_2985882 : CollatzResearch.WordTrace tailWord_2985882 prefixEnd_2985882 1533192643608191956643185 := by
  unfold tailWord_2985882
  simp only [CollatzResearch.WordTrace]
  refine ⟨27226015842166734222917975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72602708912444624594447933 27226015842166734222917975)
  ·
    refine ⟨40839023763250101334376963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27226015842166734222917975 40839023763250101334376963)
    ·
      refine ⟨61258535644875152001565445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40839023763250101334376963 61258535644875152001565445)
      ·
        refine ⟨11485975433414091000293521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61258535644875152001565445 11485975433414091000293521)
        ·
          refine ⟨8614481575060568250220141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11485975433414091000293521 8614481575060568250220141)
          ·
            refine ⟨3230430590647713093832553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8614481575060568250220141 3230430590647713093832553)
            ·
              refine ⟨2422822942985784820374415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3230430590647713093832553 2422822942985784820374415)
              ·
                refine ⟨3634234414478677230561623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2422822942985784820374415 3634234414478677230561623)
                ·
                  refine ⟨5451351621718015845842435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3634234414478677230561623 5451351621718015845842435)
                  ·
                    refine ⟨8177027432577023768763653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5451351621718015845842435 8177027432577023768763653)
                    ·
                      refine ⟨1533192643608191956643185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8177027432577023768763653 1533192643608191956643185)
                      ·
                        rfl

theorem cell23_2985882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_2985882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985882 prefixEnd_2985882 := by exact prefixLift 2985882
  have htrace : WordTrace (prefixWord ++ tailWord_2985882) baseStart_2985882 baseEnd_2985882 := by
    simpa [prefixWord, tailWord_2985882, baseEnd_2985882] using wordTrace_append hprefix tailTrace_2985882
  have hstable : (prefixWord ++ tailWord_2985882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985882).length < 2 ^ (prefixWord ++ tailWord_2985882).sum := by decide
  have hdescent : baseEnd_2985882 < baseStart_2985882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2985885 : List Nat := [1, 4, 2, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_2985885 : Nat := 118140960795 + 2985885 * 2 ^ 59
def prefixEnd_2985885 : Nat := 4983230072969 + 3 ^ 40 * 2985885 * 2
def baseEnd_2985885 : Nat := 1533194184050155444905671

theorem tailTrace_2985885 : CollatzResearch.WordTrace tailWord_2985885 prefixEnd_2985885 1533194184050155444905671 := by
  unfold tailWord_2985885
  simp only [CollatzResearch.WordTrace]
  refine ⟨108904172787656068404031109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72602781858437378936020739 108904172787656068404031109)
  ·
    refine ⟨20419532397685512825755833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108904172787656068404031109 20419532397685512825755833)
    ·
      refine ⟨15314649298264134619316875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20419532397685512825755833 15314649298264134619316875)
      ·
        refine ⟨22971973947396201928975313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15314649298264134619316875 22971973947396201928975313)
        ·
          refine ⟨17228980460547151446731485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22971973947396201928975313 17228980460547151446731485)
          ·
            refine ⟨6460867672705181792524307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17228980460547151446731485 6460867672705181792524307)
            ·
              refine ⟨9691301509057772688786461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6460867672705181792524307 9691301509057772688786461)
              ·
                refine ⟨3634238065896664758294923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9691301509057772688786461 3634238065896664758294923)
                ·
                  refine ⟨5451357098844997137442385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3634238065896664758294923 5451357098844997137442385)
                  ·
                    refine ⟨4088517824133747853081789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5451357098844997137442385 4088517824133747853081789)
                    ·
                      refine ⟨1533194184050155444905671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4088517824133747853081789 1533194184050155444905671)
                      ·
                        rfl

theorem cell23_2985885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_2985885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2985885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2985885 prefixEnd_2985885 := by exact prefixLift 2985885
  have htrace : WordTrace (prefixWord ++ tailWord_2985885) baseStart_2985885 baseEnd_2985885 := by
    simpa [prefixWord, tailWord_2985885, baseEnd_2985885] using wordTrace_append hprefix tailTrace_2985885
  have hstable : (prefixWord ++ tailWord_2985885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2985885).length < 2 ^ (prefixWord ++ tailWord_2985885).sum := by decide
  have hdescent : baseEnd_2985885 < baseStart_2985885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2985885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986008 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 2, 5]
def baseStart_2986008 : Nat := 118140960795 + 2986008 * 2 ^ 59
def prefixEnd_2986008 : Nat := 4983230072969 + 3 ^ 40 * 2986008 * 2
def baseEnd_2986008 : Nat := 511085780723552821222535

theorem tailTrace_2986008 : CollatzResearch.WordTrace tailWord_2986008 prefixEnd_2986008 511085780723552821222535 := by
  unfold tailWord_2986008
  simp only [CollatzResearch.WordTrace]
  refine ⟨54454329483105230205379339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72605772644140306940505785 54454329483105230205379339)
  ·
    refine ⟨81681494224657845308069009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54454329483105230205379339 81681494224657845308069009)
    ·
      refine ⟨61261120668493383981051757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81681494224657845308069009 61261120668493383981051757)
      ·
        refine ⟨22972920250685018992894409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61261120668493383981051757 22972920250685018992894409)
        ·
          refine ⟨17229690188013764244670807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22972920250685018992894409 17229690188013764244670807)
          ·
            refine ⟨25844535282020646367006211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17229690188013764244670807 25844535282020646367006211)
            ·
              refine ⟨38766802923030969550509317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25844535282020646367006211 38766802923030969550509317)
              ·
                refine ⟨7268775548068306790720497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38766802923030969550509317 7268775548068306790720497)
                ·
                  refine ⟨5451581661051230093040373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7268775548068306790720497 5451581661051230093040373)
                  ·
                    refine ⟨511085780723552821222535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5451581661051230093040373 511085780723552821222535)
                    ·
                      rfl

theorem cell23_2986008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_2986008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986008 prefixEnd_2986008 := by exact prefixLift 2986008
  have htrace : WordTrace (prefixWord ++ tailWord_2986008) baseStart_2986008 baseEnd_2986008 := by
    simpa [prefixWord, tailWord_2986008, baseEnd_2986008] using wordTrace_append hprefix tailTrace_2986008
  have hstable : (prefixWord ++ tailWord_2986008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986008).length < 2 ^ (prefixWord ++ tailWord_2986008).sum := by decide
  have hdescent : baseEnd_2986008 < baseStart_2986008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986012 : List Nat := [2, 2, 3, 1, 3, 1, 4, 2, 5]
def baseStart_2986012 : Nat := 118140960795 + 2986012 * 2 ^ 59
def prefixEnd_2986012 : Nat := 4983230072969 + 3 ^ 40 * 2986012 * 2
def baseEnd_2986012 : Nat := 170362155121475160890843

theorem tailTrace_2986012 : CollatzResearch.WordTrace tailWord_2986012 prefixEnd_2986012 170362155121475160890843 := by
  unfold tailWord_2986012
  simp only [CollatzResearch.WordTrace]
  refine ⟨54454402429097984546952145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72605869905463979395936193 54454402429097984546952145)
  ·
    refine ⟨40840801821823488410214109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54454402429097984546952145 40840801821823488410214109)
    ·
      refine ⟨15315300683183808153830291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40840801821823488410214109 15315300683183808153830291)
      ·
        refine ⟨22972951024775712230745437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15315300683183808153830291 22972951024775712230745437)
        ·
          refine ⟨8614856634290892086529539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22972951024775712230745437 8614856634290892086529539)
          ·
            refine ⟨12922284951436338129794309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8614856634290892086529539 12922284951436338129794309)
            ·
              refine ⟨2422928428394313399336433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12922284951436338129794309 2422928428394313399336433)
              ·
                refine ⟨1817196321295735049502325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2422928428394313399336433 1817196321295735049502325)
                ·
                  refine ⟨170362155121475160890843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1817196321295735049502325 170362155121475160890843)
                  ·
                    rfl

theorem cell23_2986012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 5].length) (baseStart_2986012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986012 prefixEnd_2986012 := by exact prefixLift 2986012
  have htrace : WordTrace (prefixWord ++ tailWord_2986012) baseStart_2986012 baseEnd_2986012 := by
    simpa [prefixWord, tailWord_2986012, baseEnd_2986012] using wordTrace_append hprefix tailTrace_2986012
  have hstable : (prefixWord ++ tailWord_2986012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986012).length < 2 ^ (prefixWord ++ tailWord_2986012).sum := by decide
  have hdescent : baseEnd_2986012 < baseStart_2986012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986018 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_2986018 : Nat := 118140960795 + 2986018 * 2 ^ 59
def prefixEnd_2986018 : Nat := 4983230072969 + 3 ^ 40 * 2986018 * 2
def baseEnd_2986018 : Nat := 1533262476977203424542559

theorem tailTrace_2986018 : CollatzResearch.WordTrace tailWord_2986018 prefixEnd_2986018 1533262476977203424542559 := by
  unfold tailWord_2986018
  simp only [CollatzResearch.WordTrace]
  refine ⟨27227255924043558029655677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72606015797449488079081805 27227255924043558029655677)
  ·
    refine ⟨10210220971516334261120879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27227255924043558029655677 10210220971516334261120879)
    ·
      refine ⟨15315331457274501391681319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10210220971516334261120879 15315331457274501391681319)
      ·
        refine ⟨22972997185911752087521979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15315331457274501391681319 22972997185911752087521979)
        ·
          refine ⟨34459495778867628131282969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22972997185911752087521979 34459495778867628131282969)
          ·
            refine ⟨25844621834150721098462227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34459495778867628131282969 25844621834150721098462227)
            ·
              refine ⟨38766932751226081647693341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25844621834150721098462227 38766932751226081647693341)
              ·
                refine ⟨14537599781709780617885003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38766932751226081647693341 14537599781709780617885003)
                ·
                  refine ⟨21806399672564670926827505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14537599781709780617885003 21806399672564670926827505)
                  ·
                    refine ⟨16354799754423503195120629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21806399672564670926827505 16354799754423503195120629)
                    ·
                      refine ⟨1533262476977203424542559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16354799754423503195120629 1533262476977203424542559)
                      ·
                        rfl

theorem cell23_2986018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_2986018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986018 prefixEnd_2986018 := by exact prefixLift 2986018
  have htrace : WordTrace (prefixWord ++ tailWord_2986018) baseStart_2986018 baseEnd_2986018 := by
    simpa [prefixWord, tailWord_2986018, baseEnd_2986018] using wordTrace_append hprefix tailTrace_2986018
  have hstable : (prefixWord ++ tailWord_2986018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986018).length < 2 ^ (prefixWord ++ tailWord_2986018).sum := by decide
  have hdescent : baseEnd_2986018 < baseStart_2986018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986045 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 1, 6, 2]
def baseStart_2986045 : Nat := 118140960795 + 2986045 * 2 ^ 59
def prefixEnd_2986045 : Nat := 4983230072969 + 3 ^ 40 * 2986045 * 2
def baseEnd_2986045 : Nat := 1533276340954874818904935

theorem tailTrace_2986045 : CollatzResearch.WordTrace tailWord_2986045 prefixEnd_2986045 1533276340954874818904935 := by
  unfold tailWord_2986045
  simp only [CollatzResearch.WordTrace]
  refine ⟨108910008467076415729855589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72606672311384277153237059 108910008467076415729855589)
  ·
    refine ⟨20420626587576827949347923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108910008467076415729855589 20420626587576827949347923)
    ·
      refine ⟨30630939881365241924021885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20420626587576827949347923 30630939881365241924021885)
      ·
        refine ⟨11486602455511965721508207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30630939881365241924021885 11486602455511965721508207)
        ·
          refine ⟨17229903683267948582262311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11486602455511965721508207 17229903683267948582262311)
          ·
            refine ⟨25844855524901922873393467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17229903683267948582262311 25844855524901922873393467)
            ·
              refine ⟨38767283287352884310090201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25844855524901922873393467 38767283287352884310090201)
              ·
                refine ⟨29075462465514663232567651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38767283287352884310090201 29075462465514663232567651)
                ·
                  refine ⟨43613193698271994848851477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29075462465514663232567651 43613193698271994848851477)
                  ·
                    refine ⟨2044368454606499758539913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43613193698271994848851477 2044368454606499758539913)
                    ·
                      refine ⟨1533276340954874818904935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2044368454606499758539913 1533276340954874818904935)
                      ·
                        rfl

theorem cell23_2986045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_2986045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986045 prefixEnd_2986045 := by exact prefixLift 2986045
  have htrace : WordTrace (prefixWord ++ tailWord_2986045) baseStart_2986045 baseEnd_2986045 := by
    simpa [prefixWord, tailWord_2986045, baseEnd_2986045] using wordTrace_append hprefix tailTrace_2986045
  have hstable : (prefixWord ++ tailWord_2986045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986045).length < 2 ^ (prefixWord ++ tailWord_2986045).sum := by decide
  have hdescent : baseEnd_2986045 < baseStart_2986045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986072 : List Nat := [2, 1, 2, 2, 1, 4, 2, 4, 1, 4]
def baseStart_2986072 : Nat := 118140960795 + 2986072 * 2 ^ 59
def prefixEnd_2986072 : Nat := 4983230072969 + 3 ^ 40 * 2986072 * 2
def baseEnd_2986072 : Nat := 511096734977515404422437

theorem tailTrace_2986072 : CollatzResearch.WordTrace tailWord_2986072 prefixEnd_2986072 511096734977515404422437 := by
  unfold tailWord_2986072
  simp only [CollatzResearch.WordTrace]
  refine ⟨54455496618989299670544235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72607328825319066227392313 54455496618989299670544235)
  ·
    refine ⟨81683244928483949505816353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54455496618989299670544235 81683244928483949505816353)
    ·
      refine ⟨61262433696362962129362265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81683244928483949505816353 61262433696362962129362265)
      ·
        refine ⟨45946825272272221597021699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61262433696362962129362265 45946825272272221597021699)
        ·
          refine ⟨68920237908408332395532549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45946825272272221597021699 68920237908408332395532549)
          ·
            refine ⟨12922544607826562324162353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68920237908408332395532549 12922544607826562324162353)
            ·
              refine ⟨9691908455869921743121765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12922544607826562324162353 9691908455869921743121765)
              ·
                refine ⟨1817232835475610326835331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9691908455869921743121765 1817232835475610326835331)
                ·
                  refine ⟨2725849253213415490252997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817232835475610326835331 2725849253213415490252997)
                  ·
                    refine ⟨511096734977515404422437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2725849253213415490252997 511096734977515404422437)
                    ·
                      rfl

theorem cell23_2986072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 1, 4].length) (baseStart_2986072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986072 prefixEnd_2986072 := by exact prefixLift 2986072
  have htrace : WordTrace (prefixWord ++ tailWord_2986072) baseStart_2986072 baseEnd_2986072 := by
    simpa [prefixWord, tailWord_2986072, baseEnd_2986072] using wordTrace_append hprefix tailTrace_2986072
  have hstable : (prefixWord ++ tailWord_2986072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986072).length < 2 ^ (prefixWord ++ tailWord_2986072).sum := by decide
  have hdescent : baseEnd_2986072 < baseStart_2986072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986115 : List Nat := [1, 1, 1, 3, 3, 3, 2, 3, 1, 5]
def baseStart_2986115 : Nat := 118140960795 + 2986115 * 2 ^ 59
def prefixEnd_2986115 : Nat := 4983230072969 + 3 ^ 40 * 2986115 * 2
def baseEnd_2986115 : Nat := 511104094866896515009871

theorem tailTrace_2986115 : CollatzResearch.WordTrace tailWord_2986115 prefixEnd_2986115 511104094866896515009871 := by
  unfold tailWord_2986115
  simp only [CollatzResearch.WordTrace]
  refine ⟨108912561576822817684903799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72608374384548545123269199 108912561576822817684903799)
  ·
    refine ⟨163368842365234226527355699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108912561576822817684903799 163368842365234226527355699)
    ·
      refine ⟨245053263547851339791033549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163368842365234226527355699 245053263547851339791033549)
      ·
        refine ⟨91894973830444252421637581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245053263547851339791033549 91894973830444252421637581)
        ·
          refine ⟨34460615186416594658114093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91894973830444252421637581 34460615186416594658114093)
          ·
            refine ⟨12922730694906222996792785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34460615186416594658114093 12922730694906222996792785)
            ·
              refine ⟨9692048021179667247594589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12922730694906222996792785 9692048021179667247594589)
              ·
                refine ⟨3634518007942375217847971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9692048021179667247594589 3634518007942375217847971)
                ·
                  refine ⟨5451777011913562826771957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3634518007942375217847971 5451777011913562826771957)
                  ·
                    refine ⟨511104094866896515009871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5451777011913562826771957 511104094866896515009871)
                    ·
                      rfl

theorem cell23_2986115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 5].length) (baseStart_2986115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986115 prefixEnd_2986115 := by exact prefixLift 2986115
  have htrace : WordTrace (prefixWord ++ tailWord_2986115) baseStart_2986115 baseEnd_2986115 := by
    simpa [prefixWord, tailWord_2986115, baseEnd_2986115] using wordTrace_append hprefix tailTrace_2986115
  have hstable : (prefixWord ++ tailWord_2986115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986115).length < 2 ^ (prefixWord ++ tailWord_2986115).sum := by decide
  have hdescent : baseEnd_2986115 < baseStart_2986115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986122 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 4, 3, 2]
def baseStart_2986122 : Nat := 118140960795 + 2986122 * 2 ^ 59
def prefixEnd_2986122 : Nat := 4983230072969 + 3 ^ 40 * 2986122 * 2
def baseEnd_2986122 : Nat := 1533315878965271017642081

theorem tailTrace_2986122 : CollatzResearch.WordTrace tailWord_2986122 prefixEnd_2986122 1533315878965271017642081 := by
  unfold tailWord_2986122
  simp only [CollatzResearch.WordTrace]
  refine ⟨27228204221949364470102155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72608544591864971920272413 27228204221949364470102155)
  ·
    refine ⟨40842306332924046705153233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27228204221949364470102155 40842306332924046705153233)
    ·
      refine ⟨30631729749693035028864925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40842306332924046705153233 30631729749693035028864925)
      ·
        refine ⟨11486898656134888135824347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30631729749693035028864925 11486898656134888135824347)
        ·
          refine ⟨17230347984202332203736521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11486898656134888135824347 17230347984202332203736521)
          ·
            refine ⟨12922760988151749152802391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17230347984202332203736521 12922760988151749152802391)
            ·
              refine ⟨19384141482227623729203587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12922760988151749152802391 19384141482227623729203587)
              ·
                refine ⟨29076212223341435593805381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19384141482227623729203587 29076212223341435593805381)
                ·
                  refine ⟨5451789791876519173838509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29076212223341435593805381 5451789791876519173838509)
                  ·
                    refine ⟨2044421171953694690189441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5451789791876519173838509 2044421171953694690189441)
                    ·
                      refine ⟨1533315878965271017642081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2044421171953694690189441 1533315878965271017642081)
                      ·
                        rfl

theorem cell23_2986122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_2986122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986122 prefixEnd_2986122 := by exact prefixLift 2986122
  have htrace : WordTrace (prefixWord ++ tailWord_2986122) baseStart_2986122 baseEnd_2986122 := by
    simpa [prefixWord, tailWord_2986122, baseEnd_2986122] using wordTrace_append hprefix tailTrace_2986122
  have hstable : (prefixWord ++ tailWord_2986122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986122).length < 2 ^ (prefixWord ++ tailWord_2986122).sum := by decide
  have hdescent : baseEnd_2986122 < baseStart_2986122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986186 : List Nat := [3, 1, 2, 1, 3, 1, 3, 4, 1, 2, 2]
def baseStart_2986186 : Nat := 118140960795 + 2986186 * 2 ^ 59
def prefixEnd_2986186 : Nat := 4983230072969 + 3 ^ 40 * 2986186 * 2
def baseEnd_2986186 : Nat := 1533348741727158767241787

theorem tailTrace_2986186 : CollatzResearch.WordTrace tailWord_2986186 prefixEnd_2986186 1533348741727158767241787 := by
  unfold tailWord_2986186
  simp only [CollatzResearch.WordTrace]
  refine ⟨27228787789891399202684603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72610100773043731207158941 27228787789891399202684603)
  ·
    refine ⟨40843181684837098804026905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27228787789891399202684603 40843181684837098804026905)
    ·
      refine ⟨30632386263627824103020179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40843181684837098804026905 30632386263627824103020179)
      ·
        refine ⟨45948579395441736154530269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30632386263627824103020179 45948579395441736154530269)
        ·
          refine ⟨17230717273290651057948851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45948579395441736154530269 17230717273290651057948851)
          ·
            refine ⟨25846075909935976586923277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17230717273290651057948851 25846075909935976586923277)
            ·
              refine ⟨9692278466225991220096229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25846075909935976586923277 9692278466225991220096229)
              ·
                refine ⟨1817302212417373353768043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9692278466225991220096229 1817302212417373353768043)
                ·
                  refine ⟨2725953318626060030652065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817302212417373353768043 2725953318626060030652065)
                  ·
                    refine ⟨2044464988969545022989049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2725953318626060030652065 2044464988969545022989049)
                    ·
                      refine ⟨1533348741727158767241787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2044464988969545022989049 1533348741727158767241787)
                      ·
                        rfl

theorem cell23_2986186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_2986186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986186 prefixEnd_2986186 := by exact prefixLift 2986186
  have htrace : WordTrace (prefixWord ++ tailWord_2986186) baseStart_2986186 baseEnd_2986186 := by
    simpa [prefixWord, tailWord_2986186, baseEnd_2986186] using wordTrace_append hprefix tailTrace_2986186
  have hstable : (prefixWord ++ tailWord_2986186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986186).length < 2 ^ (prefixWord ++ tailWord_2986186).sum := by decide
  have hdescent : baseEnd_2986186 < baseStart_2986186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986195 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 1, 9, 2]
def baseStart_2986195 : Nat := 118140960795 + 2986195 * 2 ^ 59
def prefixEnd_2986195 : Nat := 4983230072969 + 3 ^ 40 * 2986195 * 2
def baseEnd_2986195 : Nat := 1533353363053049232029245

theorem tailTrace_2986195 : CollatzResearch.WordTrace tailWord_2986195 prefixEnd_2986195 1533353363053049232029245 := by
  unfold tailWord_2986195
  simp only [CollatzResearch.WordTrace]
  refine ⟨108915479416532991347816039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72610319611021994231877359 108915479416532991347816039)
  ·
    refine ⟨163373219124799487021724059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108915479416532991347816039 163373219124799487021724059)
    ·
      refine ⟨245059828687199230532586089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163373219124799487021724059 245059828687199230532586089)
      ·
        refine ⟨183794871515399422899439567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245059828687199230532586089 183794871515399422899439567)
        ·
          refine ⟨275692307273099134349159351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183794871515399422899439567 275692307273099134349159351)
          ·
            refine ⟨413538460909648701523739027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275692307273099134349159351 413538460909648701523739027)
            ·
              refine ⟨620307691364473052285608541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413538460909648701523739027 620307691364473052285608541)
              ·
                refine ⟨232615384261677394607103203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 620307691364473052285608541 232615384261677394607103203)
                ·
                  refine ⟨348923076392516091910654805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232615384261677394607103203 348923076392516091910654805)
                  ·
                    refine ⟨2044471150737398976038993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 348923076392516091910654805 2044471150737398976038993)
                    ·
                      refine ⟨1533353363053049232029245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2044471150737398976038993 1533353363053049232029245)
                      ·
                        rfl

theorem cell23_2986195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 9, 2].length) (baseStart_2986195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986195 prefixEnd_2986195 := by exact prefixLift 2986195
  have htrace : WordTrace (prefixWord ++ tailWord_2986195) baseStart_2986195 baseEnd_2986195 := by
    simpa [prefixWord, tailWord_2986195, baseEnd_2986195] using wordTrace_append hprefix tailTrace_2986195
  have hstable : (prefixWord ++ tailWord_2986195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986195).length < 2 ^ (prefixWord ++ tailWord_2986195).sum := by decide
  have hdescent : baseEnd_2986195 < baseStart_2986195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986236 : List Nat := [2, 2, 2, 1, 4, 3, 1, 2, 2, 1, 3]
def baseStart_2986236 : Nat := 118140960795 + 2986236 * 2 ^ 59
def prefixEnd_2986236 : Nat := 4983230072969 + 3 ^ 40 * 2986236 * 2
def baseEnd_2986236 : Nat := 1533374415759883571616557

theorem tailTrace_2986236 : CollatzResearch.WordTrace tailWord_2986236 prefixEnd_2986236 1533374415759883571616557 := by
  unfold tailWord_2986236
  simp only [CollatzResearch.WordTrace]
  refine ⟨54458487404692227675029281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72611316539589636900039041 54458487404692227675029281)
  ·
    refine ⟨40843865553519170756271961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54458487404692227675029281 40843865553519170756271961)
    ·
      refine ⟨30632899165139378067203971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40843865553519170756271961 30632899165139378067203971)
      ·
        refine ⟨45949348747709067100805957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30632899165139378067203971 45949348747709067100805957)
        ·
          refine ⟨8615502890195450081401117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45949348747709067100805957 8615502890195450081401117)
          ·
            refine ⟨3230813583823293780525419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8615502890195450081401117 3230813583823293780525419)
            ·
              refine ⟨4846220375734940670788129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3230813583823293780525419 4846220375734940670788129)
              ·
                refine ⟨3634665281801205503091097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4846220375734940670788129 3634665281801205503091097)
                ·
                  refine ⟨2725998961350904127318323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3634665281801205503091097 2725998961350904127318323)
                  ·
                    refine ⟨4088998442026356190977485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2725998961350904127318323 4088998442026356190977485)
                    ·
                      refine ⟨1533374415759883571616557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4088998442026356190977485 1533374415759883571616557)
                      ·
                        rfl

theorem cell23_2986236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_2986236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986236 prefixEnd_2986236 := by exact prefixLift 2986236
  have htrace : WordTrace (prefixWord ++ tailWord_2986236) baseStart_2986236 baseEnd_2986236 := by
    simpa [prefixWord, tailWord_2986236, baseEnd_2986236] using wordTrace_append hprefix tailTrace_2986236
  have hstable : (prefixWord ++ tailWord_2986236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986236).length < 2 ^ (prefixWord ++ tailWord_2986236).sum := by decide
  have hdescent : baseEnd_2986236 < baseStart_2986236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986245 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 2, 4, 3]
def baseStart_2986245 : Nat := 118140960795 + 2986245 * 2 ^ 59
def prefixEnd_2986245 : Nat := 4983230072969 + 3 ^ 40 * 2986245 * 2
def baseEnd_2986245 : Nat := 1533379037085774036404015

theorem tailTrace_2986245 : CollatzResearch.WordTrace tailWord_2986245 prefixEnd_2986245 1533379037085774036404015 := by
  unfold tailWord_2986245
  simp only [CollatzResearch.WordTrace]
  refine ⟨108917303066351849887136189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72611535377567899924757459 108917303066351849887136189)
  ·
    refine ⟨40843988649881943707676071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108917303066351849887136189 40843988649881943707676071)
    ·
      refine ⟨61265982974822915561514107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40843988649881943707676071 61265982974822915561514107)
      ·
        refine ⟨91898974462234373342271161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61265982974822915561514107 91898974462234373342271161)
        ·
          refine ⟨68924230846675780006703371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91898974462234373342271161 68924230846675780006703371)
          ·
            refine ⟨103386346270013670010055057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68924230846675780006703371 103386346270013670010055057)
            ·
              refine ⟨77539759702510252507541293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103386346270013670010055057 77539759702510252507541293)
              ·
                refine ⟨29077409888441344690327985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77539759702510252507541293 29077409888441344690327985)
                ·
                  refine ⟨21808057416331008517745989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29077409888441344690327985 21808057416331008517745989)
                  ·
                    refine ⟨4089010765562064097077373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21808057416331008517745989 4089010765562064097077373)
                    ·
                      refine ⟨1533379037085774036404015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4089010765562064097077373 1533379037085774036404015)
                      ·
                        rfl

theorem cell23_2986245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_2986245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986245 prefixEnd_2986245 := by exact prefixLift 2986245
  have htrace : WordTrace (prefixWord ++ tailWord_2986245) baseStart_2986245 baseEnd_2986245 := by
    simpa [prefixWord, tailWord_2986245, baseEnd_2986245] using wordTrace_append hprefix tailTrace_2986245
  have hstable : (prefixWord ++ tailWord_2986245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986245).length < 2 ^ (prefixWord ++ tailWord_2986245).sum := by decide
  have hdescent : baseEnd_2986245 < baseStart_2986245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986259 : List Nat := [1, 1, 1, 2, 1, 3, 1, 7, 2, 2, 2]
def baseStart_2986259 : Nat := 118140960795 + 2986259 * 2 ^ 59
def prefixEnd_2986259 : Nat := 4983230072969 + 3 ^ 40 * 2986259 * 2
def baseEnd_2986259 : Nat := 1533386225814936981628951

theorem tailTrace_2986259 : CollatzResearch.WordTrace tailWord_2986259 prefixEnd_2986259 1533386225814936981628951 := by
  unfold tailWord_2986259
  simp only [CollatzResearch.WordTrace]
  refine ⟨108917813688301130278145831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72611875792200753518763887 108917813688301130278145831)
  ·
    refine ⟨163376720532451695417218747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108917813688301130278145831 163376720532451695417218747)
    ·
      refine ⟨245065080798677543125828121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163376720532451695417218747 245065080798677543125828121)
      ·
        refine ⟨183798810599008157344371091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245065080798677543125828121 183798810599008157344371091)
        ·
          refine ⟨275698215898512236016556637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183798810599008157344371091 275698215898512236016556637)
          ·
            refine ⟨103386830961942088506208739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275698215898512236016556637 103386830961942088506208739)
            ·
              refine ⟨155080246442913132759313109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103386830961942088506208739 155080246442913132759313109)
              ·
                refine ⟨3634693276005776549046401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 155080246442913132759313109 3634693276005776549046401)
                ·
                  refine ⟨2726019957004332411784801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3634693276005776549046401 2726019957004332411784801)
                  ·
                    refine ⟨2044514967753249308838601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2726019957004332411784801 2044514967753249308838601)
                    ·
                      refine ⟨1533386225814936981628951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2044514967753249308838601 1533386225814936981628951)
                      ·
                        rfl

theorem cell23_2986259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 2, 2].length) (baseStart_2986259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986259 prefixEnd_2986259 := by exact prefixLift 2986259
  have htrace : WordTrace (prefixWord ++ tailWord_2986259) baseStart_2986259 baseEnd_2986259 := by
    simpa [prefixWord, tailWord_2986259, baseEnd_2986259] using wordTrace_append hprefix tailTrace_2986259
  have hstable : (prefixWord ++ tailWord_2986259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986259).length < 2 ^ (prefixWord ++ tailWord_2986259).sum := by decide
  have hdescent : baseEnd_2986259 < baseStart_2986259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986315 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 4]
def baseStart_2986315 : Nat := 118140960795 + 2986315 * 2 ^ 59
def prefixEnd_2986315 : Nat := 4983230072969 + 3 ^ 40 * 2986315 * 2
def baseEnd_2986315 : Nat := 1533414980731588762528693

theorem tailTrace_2986315 : CollatzResearch.WordTrace tailWord_2986315 prefixEnd_2986315 1533414980731588762528693 := by
  unfold tailWord_2986315
  simp only [CollatzResearch.WordTrace]
  refine ⟨108919856176098251842184399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72613237450732167894789599 108919856176098251842184399)
  ·
    refine ⟨163379784264147377763276599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108919856176098251842184399 163379784264147377763276599)
    ·
      refine ⟨245069676396221066644914899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163379784264147377763276599 245069676396221066644914899)
      ·
        refine ⟨367604514594331599967372349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245069676396221066644914899 367604514594331599967372349)
        ·
          refine ⟨137851692972874349987764631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367604514594331599967372349 137851692972874349987764631)
          ·
            refine ⟨206777539459311524981646947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137851692972874349987764631 206777539459311524981646947)
            ·
              refine ⟨310166309188967287472470421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206777539459311524981646947 310166309188967287472470421)
              ·
                refine ⟨14539045743232841600272051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 310166309188967287472470421 14539045743232841600272051)
                ·
                  refine ⟨21808568614849262400408077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14539045743232841600272051 21808568614849262400408077)
                  ·
                    refine ⟨8178213230568473400153029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21808568614849262400408077 8178213230568473400153029)
                    ·
                      refine ⟨1533414980731588762528693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8178213230568473400153029 1533414980731588762528693)
                      ·
                        rfl

theorem cell23_2986315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 4].length) (baseStart_2986315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986315 prefixEnd_2986315 := by exact prefixLift 2986315
  have htrace : WordTrace (prefixWord ++ tailWord_2986315) baseStart_2986315 baseEnd_2986315 := by
    simpa [prefixWord, tailWord_2986315, baseEnd_2986315] using wordTrace_append hprefix tailTrace_2986315
  have hstable : (prefixWord ++ tailWord_2986315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986315).length < 2 ^ (prefixWord ++ tailWord_2986315).sum := by decide
  have hdescent : baseEnd_2986315 < baseStart_2986315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986345 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 2, 1, 6]
def baseStart_2986345 : Nat := 118140960795 + 2986345 * 2 ^ 59
def prefixEnd_2986345 : Nat := 4983230072969 + 3 ^ 40 * 2986345 * 2
def baseEnd_2986345 : Nat := 1533430385151223645153555

theorem tailTrace_2986345 : CollatzResearch.WordTrace tailWord_2986345 prefixEnd_2986345 1533430385151223645153555 := by
  unfold tailWord_2986345
  simp only [CollatzResearch.WordTrace]
  refine ⟨108920950365989566965776489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72613966910659711310517659 108920950365989566965776489)
  ·
    refine ⟨81690712774492175224332367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108920950365989566965776489 81690712774492175224332367)
    ·
      refine ⟨122536069161738262836498551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81690712774492175224332367 122536069161738262836498551)
      ·
        refine ⟨183804103742607394254747827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122536069161738262836498551 183804103742607394254747827)
        ·
          refine ⟨275706155613911091382121741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183804103742607394254747827 275706155613911091382121741)
          ·
            refine ⟨103389808355216659268295653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275706155613911091382121741 103389808355216659268295653)
            ·
              refine ⟨19385589066603123612805435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103389808355216659268295653 19385589066603123612805435)
              ·
                refine ⟨29078383599904685419208153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19385589066603123612805435 29078383599904685419208153)
                ·
                  refine ⟨21808787699928514064406115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29078383599904685419208153 21808787699928514064406115)
                  ·
                    refine ⟨32713181549892771096609173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21808787699928514064406115 32713181549892771096609173)
                    ·
                      refine ⟨1533430385151223645153555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32713181549892771096609173 1533430385151223645153555)
                      ·
                        rfl

theorem cell23_2986345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_2986345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986345 prefixEnd_2986345 := by exact prefixLift 2986345
  have htrace : WordTrace (prefixWord ++ tailWord_2986345) baseStart_2986345 baseEnd_2986345 := by
    simpa [prefixWord, tailWord_2986345, baseEnd_2986345] using wordTrace_append hprefix tailTrace_2986345
  have hstable : (prefixWord ++ tailWord_2986345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986345).length < 2 ^ (prefixWord ++ tailWord_2986345).sum := by decide
  have hdescent : baseEnd_2986345 < baseStart_2986345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986349 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 2, 4, 2]
def baseStart_2986349 : Nat := 118140960795 + 2986349 * 2 ^ 59
def prefixEnd_2986349 : Nat := 4983230072969 + 3 ^ 40 * 2986349 * 2
def baseEnd_2986349 : Nat := 1533432439073841629503537

theorem tailTrace_2986349 : CollatzResearch.WordTrace tailWord_2986349 prefixEnd_2986349 1533432439073841629503537 := by
  unfold tailWord_2986349
  simp only [CollatzResearch.WordTrace]
  refine ⟨108921096257975075648922101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72614064171983383765948067 108921096257975075648922101)
  ·
    refine ⟨10211352774185163342086447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108921096257975075648922101 10211352774185163342086447)
    ·
      refine ⟨15317029161277745013129671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10211352774185163342086447 15317029161277745013129671)
      ·
        refine ⟨22975543741916617519694507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15317029161277745013129671 22975543741916617519694507)
        ·
          refine ⟨34463315612874926279541761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22975543741916617519694507 34463315612874926279541761)
          ·
            refine ⟨25847486709656194709656321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34463315612874926279541761 25847486709656194709656321)
            ·
              refine ⟨19385615032242146032242241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25847486709656194709656321 19385615032242146032242241)
              ·
                refine ⟨14539211274181609524181681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19385615032242146032242241 14539211274181609524181681)
                ·
                  refine ⟨10904408455636207143136261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14539211274181609524181681 10904408455636207143136261)
                  ·
                    refine ⟨2044576585431788839338049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10904408455636207143136261 2044576585431788839338049)
                    ·
                      refine ⟨1533432439073841629503537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2044576585431788839338049 1533432439073841629503537)
                      ·
                        rfl

theorem cell23_2986349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_2986349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986349 prefixEnd_2986349 := by exact prefixLift 2986349
  have htrace : WordTrace (prefixWord ++ tailWord_2986349) baseStart_2986349 baseEnd_2986349 := by
    simpa [prefixWord, tailWord_2986349, baseEnd_2986349] using wordTrace_append hprefix tailTrace_2986349
  have hstable : (prefixWord ++ tailWord_2986349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986349).length < 2 ^ (prefixWord ++ tailWord_2986349).sum := by decide
  have hdescent : baseEnd_2986349 < baseStart_2986349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986372 : List Nat := [2, 3, 2, 1, 1, 2, 1, 5, 6]
def baseStart_2986372 : Nat := 118140960795 + 2986372 * 2 ^ 59
def prefixEnd_2986372 : Nat := 4983230072969 + 3 ^ 40 * 2986372 * 2
def baseEnd_2986372 : Nat := 170382694347655004390659

theorem tailTrace_2986372 : CollatzResearch.WordTrace tailWord_2986372 prefixEnd_2986372 170382694347655004390659 := by
  unfold tailWord_2986372
  simp only [CollatzResearch.WordTrace]
  refine ⟨54460967568445875288504685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72614623424594500384672913 54460967568445875288504685)
  ·
    refine ⟨20422862838167203233189257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54460967568445875288504685 20422862838167203233189257)
    ·
      refine ⟨15317147128625402424891943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20422862838167203233189257 15317147128625402424891943)
      ·
        refine ⟨22975720692938103637337915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15317147128625402424891943 22975720692938103637337915)
        ·
          refine ⟨34463581039407155456006873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22975720692938103637337915 34463581039407155456006873)
          ·
            refine ⟨25847685779555366592005155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34463581039407155456006873 25847685779555366592005155)
            ·
              refine ⟨38771528669333049888007733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25847685779555366592005155 38771528669333049888007733)
              ·
                refine ⟨3634830812749973427000725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38771528669333049888007733 3634830812749973427000725)
                ·
                  refine ⟨170382694347655004390659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3634830812749973427000725 170382694347655004390659)
                  ·
                    rfl

theorem cell23_2986372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_2986372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986372 prefixEnd_2986372 := by exact prefixLift 2986372
  have htrace : WordTrace (prefixWord ++ tailWord_2986372) baseStart_2986372 baseEnd_2986372 := by
    simpa [prefixWord, tailWord_2986372, baseEnd_2986372] using wordTrace_append hprefix tailTrace_2986372
  have hstable : (prefixWord ++ tailWord_2986372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986372).length < 2 ^ (prefixWord ++ tailWord_2986372).sum := by decide
  have hdescent : baseEnd_2986372 < baseStart_2986372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986399 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 5, 1, 3]
def baseStart_2986399 : Nat := 118140960795 + 2986399 * 2 ^ 59
def prefixEnd_2986399 : Nat := 4983230072969 + 3 ^ 40 * 2986399 * 2
def baseEnd_2986399 : Nat := 1533458113106566433878307

theorem tailTrace_2986399 : CollatzResearch.WordTrace tailWord_2986399 prefixEnd_2986399 1533458113106566433878307 := by
  unfold tailWord_2986399
  simp only [CollatzResearch.WordTrace]
  refine ⟨108922919907793934188242251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72615279938529289458828167 108922919907793934188242251)
  ·
    refine ⟨163384379861690901282363377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108922919907793934188242251 163384379861690901282363377)
    ·
      refine ⟨122538284896268175961772533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163384379861690901282363377 122538284896268175961772533)
      ·
        refine ⟨11487964209025141496416175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122538284896268175961772533 11487964209025141496416175)
        ·
          refine ⟨17231946313537712244624263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11487964209025141496416175 17231946313537712244624263)
          ·
            refine ⟨25847919470306568366936395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17231946313537712244624263 25847919470306568366936395)
            ·
              refine ⟨38771879205459852550404593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25847919470306568366936395 38771879205459852550404593)
              ·
                refine ⟨29078909404094889412803445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38771879205459852550404593 29078909404094889412803445)
                ·
                  refine ⟨2726147756633895882450323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29078909404094889412803445 2726147756633895882450323)
                  ·
                    refine ⟨4089221634950843823675485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2726147756633895882450323 4089221634950843823675485)
                    ·
                      refine ⟨1533458113106566433878307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4089221634950843823675485 1533458113106566433878307)
                      ·
                        rfl

theorem cell23_2986399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_2986399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986399 prefixEnd_2986399 := by exact prefixLift 2986399
  have htrace : WordTrace (prefixWord ++ tailWord_2986399) baseStart_2986399 baseEnd_2986399 := by
    simpa [prefixWord, tailWord_2986399, baseEnd_2986399] using wordTrace_append hprefix tailTrace_2986399
  have hstable : (prefixWord ++ tailWord_2986399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986399).length < 2 ^ (prefixWord ++ tailWord_2986399).sum := by decide
  have hdescent : baseEnd_2986399 < baseStart_2986399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986409 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 2, 3, 2]
def baseStart_2986409 : Nat := 118140960795 + 2986409 * 2 ^ 59
def prefixEnd_2986409 : Nat := 4983230072969 + 3 ^ 40 * 2986409 * 2
def baseEnd_2986409 : Nat := 1533463247913111394753261

theorem tailTrace_2986409 : CollatzResearch.WordTrace tailWord_2986409 prefixEnd_2986409 1533463247913111394753261 := by
  unfold tailWord_2986409
  simp only [CollatzResearch.WordTrace]
  refine ⟨108923284637757705896106281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72615523091838470597404187 108923284637757705896106281)
  ·
    refine ⟨81692463478318279422079711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108923284637757705896106281 81692463478318279422079711)
    ·
      refine ⟨122538695217477419133119567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81692463478318279422079711 122538695217477419133119567)
      ·
        refine ⟨183808042826216128699679351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122538695217477419133119567 183808042826216128699679351)
        ·
          refine ⟨275712064239324193049519027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183808042826216128699679351 275712064239324193049519027)
          ·
            refine ⟨413568096358986289574278541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275712064239324193049519027 413568096358986289574278541)
            ·
              refine ⟨155088036134619858590354453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 413568096358986289574278541 155088036134619858590354453)
              ·
                refine ⟨7269751693810305871422865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 155088036134619858590354453 7269751693810305871422865)
                ·
                  refine ⟨5452313770357729403567149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7269751693810305871422865 5452313770357729403567149)
                  ·
                    refine ⟨2044617663884148526337681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5452313770357729403567149 2044617663884148526337681)
                    ·
                      refine ⟨1533463247913111394753261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2044617663884148526337681 1533463247913111394753261)
                      ·
                        rfl

theorem cell23_2986409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 3, 2].length) (baseStart_2986409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986409 prefixEnd_2986409 := by exact prefixLift 2986409
  have htrace : WordTrace (prefixWord ++ tailWord_2986409) baseStart_2986409 baseEnd_2986409 := by
    simpa [prefixWord, tailWord_2986409, baseEnd_2986409] using wordTrace_append hprefix tailTrace_2986409
  have hstable : (prefixWord ++ tailWord_2986409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986409).length < 2 ^ (prefixWord ++ tailWord_2986409).sum := by decide
  have hdescent : baseEnd_2986409 < baseStart_2986409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986410 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2986410 : Nat := 118140960795 + 2986410 * 2 ^ 59
def prefixEnd_2986410 : Nat := 4983230072969 + 3 ^ 40 * 2986410 * 2
def baseEnd_2986410 : Nat := 511154587131255296946919

theorem tailTrace_2986410 : CollatzResearch.WordTrace tailWord_2986410 prefixEnd_2986410 511154587131255296946919 := by
  unfold tailWord_2986410
  simp only [CollatzResearch.WordTrace]
  refine ⟨27230830277688520766723171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72615547407169388711261789 27230830277688520766723171)
  ·
    refine ⟨40846245416532781150084757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27230830277688520766723171 40846245416532781150084757)
    ·
      refine ⟨1914667753899974116410223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40846245416532781150084757 1914667753899974116410223)
      ·
        refine ⟨2872001630849961174615335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1914667753899974116410223 2872001630849961174615335)
        ·
          refine ⟨4308002446274941761923003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2872001630849961174615335 4308002446274941761923003)
          ·
            refine ⟨6462003669412412642884505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4308002446274941761923003 6462003669412412642884505)
            ·
              refine ⟨4846502752059309482163379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6462003669412412642884505 4846502752059309482163379)
              ·
                refine ⟨7269754128088964223245069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4846502752059309482163379 7269754128088964223245069)
                ·
                  refine ⟨2726157798033361583716901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7269754128088964223245069 2726157798033361583716901)
                  ·
                    refine ⟨511154587131255296946919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2726157798033361583716901 511154587131255296946919)
                    ·
                      rfl

theorem cell23_2986410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2986410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986410 prefixEnd_2986410 := by exact prefixLift 2986410
  have htrace : WordTrace (prefixWord ++ tailWord_2986410) baseStart_2986410 baseEnd_2986410 := by
    simpa [prefixWord, tailWord_2986410, baseEnd_2986410] using wordTrace_append hprefix tailTrace_2986410
  have hstable : (prefixWord ++ tailWord_2986410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986410).length < 2 ^ (prefixWord ++ tailWord_2986410).sum := by decide
  have hdescent : baseEnd_2986410 < baseStart_2986410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986415 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 2, 10]
def baseStart_2986415 : Nat := 118140960795 + 2986415 * 2 ^ 59
def prefixEnd_2986415 : Nat := 4983230072969 + 3 ^ 40 * 2986415 * 2
def baseEnd_2986415 : Nat := 511155442932346123759411

theorem tailTrace_2986415 : CollatzResearch.WordTrace tailWord_2986415 prefixEnd_2986415 511155442932346123759411 := by
  unfold tailWord_2986415
  simp only [CollatzResearch.WordTrace]
  refine ⟨108923503475735968920824699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72615668983823979280549799 108923503475735968920824699)
  ·
    refine ⟨163385255213603953381237049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108923503475735968920824699 163385255213603953381237049)
    ·
      refine ⟨122538941410202965035927787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163385255213603953381237049 122538941410202965035927787)
      ·
        refine ⟨183808412115304447553891681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122538941410202965035927787 183808412115304447553891681)
        ·
          refine ⟨137856309086478335665418761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183808412115304447553891681 137856309086478335665418761)
          ·
            refine ⟨103392231814858751749064071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137856309086478335665418761 103392231814858751749064071)
            ·
              refine ⟨155088347722288127623596107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103392231814858751749064071 155088347722288127623596107)
              ·
                refine ⟨232632521583432191435394161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155088347722288127623596107 232632521583432191435394161)
                ·
                  refine ⟨174474391187574143576545621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232632521583432191435394161 174474391187574143576545621)
                  ·
                    refine ⟨511155442932346123759411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 174474391187574143576545621 511155442932346123759411)
                    ·
                      rfl

theorem cell23_2986415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 10].length) (baseStart_2986415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986415 prefixEnd_2986415 := by exact prefixLift 2986415
  have htrace : WordTrace (prefixWord ++ tailWord_2986415) baseStart_2986415 baseEnd_2986415 := by
    simpa [prefixWord, tailWord_2986415, baseEnd_2986415] using wordTrace_append hprefix tailTrace_2986415
  have hstable : (prefixWord ++ tailWord_2986415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986415).length < 2 ^ (prefixWord ++ tailWord_2986415).sum := by decide
  have hdescent : baseEnd_2986415 < baseStart_2986415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986439 : List Nat := [1, 1, 4, 1, 1, 4, 1, 4, 1, 1, 4]
def baseStart_2986439 : Nat := 118140960795 + 2986439 * 2 ^ 59
def prefixEnd_2986439 : Nat := 4983230072969 + 3 ^ 40 * 2986439 * 2
def baseEnd_2986439 : Nat := 1533478652332746277378123

theorem tailTrace_2986439 : CollatzResearch.WordTrace tailWord_2986439 prefixEnd_2986439 1533478652332746277378123 := by
  unfold tailWord_2986439
  simp only [CollatzResearch.WordTrace]
  refine ⟨108924378827649021019698371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72616252551766014013132247 108924378827649021019698371)
  ·
    refine ⟨163386568241473531529547557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108924378827649021019698371 163386568241473531529547557)
    ·
      refine ⟨30634981545276287161790167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163386568241473531529547557 30634981545276287161790167)
      ·
        refine ⟨45952472317914430742685251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30634981545276287161790167 45952472317914430742685251)
        ·
          refine ⟨68928708476871646114027877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45952472317914430742685251 68928708476871646114027877)
          ·
            refine ⟨12924132839413433646380227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68928708476871646114027877 12924132839413433646380227)
            ·
              refine ⟨19386199259120150469570341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12924132839413433646380227 19386199259120150469570341)
              ·
                refine ⟨3634912361085028213044439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19386199259120150469570341 3634912361085028213044439)
                ·
                  refine ⟨5452368541627542319566659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3634912361085028213044439 5452368541627542319566659)
                  ·
                    refine ⟨8178552812441313479349989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5452368541627542319566659 8178552812441313479349989)
                    ·
                      refine ⟨1533478652332746277378123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8178552812441313479349989 1533478652332746277378123)
                      ·
                        rfl

theorem cell23_2986439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_2986439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986439 prefixEnd_2986439 := by exact prefixLift 2986439
  have htrace : WordTrace (prefixWord ++ tailWord_2986439) baseStart_2986439 baseEnd_2986439 := by
    simpa [prefixWord, tailWord_2986439, baseEnd_2986439] using wordTrace_append hprefix tailTrace_2986439
  have hstable : (prefixWord ++ tailWord_2986439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986439).length < 2 ^ (prefixWord ++ tailWord_2986439).sum := by decide
  have hdescent : baseEnd_2986439 < baseStart_2986439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986442 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_2986442 : Nat := 118140960795 + 2986442 * 2 ^ 59
def prefixEnd_2986442 : Nat := 4983230072969 + 3 ^ 40 * 2986442 * 2
def baseEnd_2986442 : Nat := 1533480192774709765640609

theorem tailTrace_2986442 : CollatzResearch.WordTrace tailWord_2986442 prefixEnd_2986442 1533480192774709765640609 := by
  unfold tailWord_2986442
  simp only [CollatzResearch.WordTrace]
  refine ⟨27231122061659538133014395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72616325497758768354705053 27231122061659538133014395)
  ·
    refine ⟨40846683092489307199521593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27231122061659538133014395 40846683092489307199521593)
    ·
      refine ⟨30635012319366980399641195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40846683092489307199521593 30635012319366980399641195)
      ·
        refine ⟨45952518479050470599461793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30635012319366980399641195 45952518479050470599461793)
        ·
          refine ⟨34464388859287852949596345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45952518479050470599461793 34464388859287852949596345)
          ·
            refine ⟨25848291644465889712197259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34464388859287852949596345 25848291644465889712197259)
            ·
              refine ⟨38772437466698834568295889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25848291644465889712197259 38772437466698834568295889)
              ·
                refine ⟨29079328100024125926221917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38772437466698834568295889 29079328100024125926221917)
                ·
                  refine ⟨10904748037509047222333219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29079328100024125926221917 10904748037509047222333219)
                  ·
                    refine ⟨16357122056263570833499829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10904748037509047222333219 16357122056263570833499829)
                    ·
                      refine ⟨1533480192774709765640609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16357122056263570833499829 1533480192774709765640609)
                      ·
                        rfl

theorem cell23_2986442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_2986442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986442 prefixEnd_2986442 := by exact prefixLift 2986442
  have htrace : WordTrace (prefixWord ++ tailWord_2986442) baseStart_2986442 baseEnd_2986442 := by
    simpa [prefixWord, tailWord_2986442, baseEnd_2986442] using wordTrace_append hprefix tailTrace_2986442
  have hstable : (prefixWord ++ tailWord_2986442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986442).length < 2 ^ (prefixWord ++ tailWord_2986442).sum := by decide
  have hdescent : baseEnd_2986442 < baseStart_2986442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986546 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2]
def baseStart_2986546 : Nat := 118140960795 + 2986546 * 2 ^ 59
def prefixEnd_2986546 : Nat := 4983230072969 + 3 ^ 40 * 2986546 * 2
def baseEnd_2986546 : Nat := 1533533594762777358740131

theorem tailTrace_2986546 : CollatzResearch.WordTrace tailWord_2986546 prefixEnd_2986546 1533533594762777358740131 := by
  unfold tailWord_2986546
  simp only [CollatzResearch.WordTrace]
  refine ⟨27232070359565344573460873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72618854292174252195895661 27232070359565344573460873)
  ·
    refine ⟨20424052769674008430095655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27232070359565344573460873 20424052769674008430095655)
    ·
      refine ⟨30636079154511012645143483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20424052769674008430095655 30636079154511012645143483)
      ·
        refine ⟨45954118731766518967715225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30636079154511012645143483 45954118731766518967715225)
        ·
          refine ⟨34465589048824889225786419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45954118731766518967715225 34465589048824889225786419)
          ·
            refine ⟨51698383573237333838679629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34465589048824889225786419 51698383573237333838679629)
            ·
              refine ⟨19386893839964000189504861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51698383573237333838679629 19386893839964000189504861)
              ·
                refine ⟨7270085189986500071064323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19386893839964000189504861 7270085189986500071064323)
                ·
                  refine ⟨10905127784979750106596485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7270085189986500071064323 10905127784979750106596485)
                  ·
                    refine ⟨2044711459683703144986841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10905127784979750106596485 2044711459683703144986841)
                    ·
                      refine ⟨1533533594762777358740131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2044711459683703144986841 1533533594762777358740131)
                      ·
                        rfl

theorem cell23_2986546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_2986546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986546 prefixEnd_2986546 := by exact prefixLift 2986546
  have htrace : WordTrace (prefixWord ++ tailWord_2986546) baseStart_2986546 baseEnd_2986546 := by
    simpa [prefixWord, tailWord_2986546, baseEnd_2986546] using wordTrace_append hprefix tailTrace_2986546
  have hstable : (prefixWord ++ tailWord_2986546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986546).length < 2 ^ (prefixWord ++ tailWord_2986546).sum := by decide
  have hdescent : baseEnd_2986546 < baseStart_2986546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986549 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_2986549 : Nat := 118140960795 + 2986549 * 2 ^ 59
def prefixEnd_2986549 : Nat := 4983230072969 + 3 ^ 40 * 2986549 * 2
def baseEnd_2986549 : Nat := 1533535135204740847002617

theorem tailTrace_2986549 : CollatzResearch.WordTrace tailWord_2986549 prefixEnd_2986549 1533535135204740847002617 := by
  unfold tailWord_2986549
  simp only [CollatzResearch.WordTrace]
  refine ⟨108928390857250509806202701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72618927238167006537468467 108928390857250509806202701)
  ·
    refine ⟨40848146571468941177326013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108928390857250509806202701 40848146571468941177326013)
    ·
      refine ⟨15318054964300852941497255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40848146571468941177326013 15318054964300852941497255)
      ·
        refine ⟨22977082446451279412245883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15318054964300852941497255 22977082446451279412245883)
        ·
          refine ⟨34465623669676919118368825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22977082446451279412245883 34465623669676919118368825)
          ·
            refine ⟨25849217752257689338776619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34465623669676919118368825 25849217752257689338776619)
            ·
              refine ⟨38773826628386534008164929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25849217752257689338776619 38773826628386534008164929)
              ·
                refine ⟨29080369971289900506123697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38773826628386534008164929 29080369971289900506123697)
                ·
                  refine ⟨21810277478467425379592773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29080369971289900506123697 21810277478467425379592773)
                  ·
                    refine ⟨4089427027212642258673645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21810277478467425379592773 4089427027212642258673645)
                    ·
                      refine ⟨1533535135204740847002617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4089427027212642258673645 1533535135204740847002617)
                      ·
                        rfl

theorem cell23_2986549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_2986549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986549 prefixEnd_2986549 := by exact prefixLift 2986549
  have htrace : WordTrace (prefixWord ++ tailWord_2986549) baseStart_2986549 baseEnd_2986549 := by
    simpa [prefixWord, tailWord_2986549, baseEnd_2986549] using wordTrace_append hprefix tailTrace_2986549
  have hstable : (prefixWord ++ tailWord_2986549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986549).length < 2 ^ (prefixWord ++ tailWord_2986549).sum := by decide
  have hdescent : baseEnd_2986549 < baseStart_2986549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986580 : List Nat := [2, 4, 1, 1, 1, 3, 3, 2, 2, 2, 2]
def baseStart_2986580 : Nat := 118140960795 + 2986580 * 2 ^ 59
def prefixEnd_2986580 : Nat := 4983230072969 + 3 ^ 40 * 2986580 * 2
def baseEnd_2986580 : Nat := 1533551053105030225714975

theorem tailTrace_2986580 : CollatzResearch.WordTrace tailWord_2986580 prefixEnd_2986580 1533551053105030225714975 := by
  unfold tailWord_2986580
  simp only [CollatzResearch.WordTrace]
  refine ⟨54464760760069101050290597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72619681013425468067054129 54464760760069101050290597)
  ·
    refine ⟨10212142642512956446929487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54464760760069101050290597 10212142642512956446929487)
    ·
      refine ⟨15318213963769434670394231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10212142642512956446929487 15318213963769434670394231)
      ·
        refine ⟨22977320945654152005591347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15318213963769434670394231 22977320945654152005591347)
        ·
          refine ⟨34465981418481228008387021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22977320945654152005591347 34465981418481228008387021)
          ·
            refine ⟨12924743031930460503145133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34465981418481228008387021 12924743031930460503145133)
            ·
              refine ⟨4846778636973922688679425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12924743031930460503145133 4846778636973922688679425)
              ·
                refine ⟨3635083977730442016509569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4846778636973922688679425 3635083977730442016509569)
                ·
                  refine ⟨2726312983297831512382177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3635083977730442016509569 2726312983297831512382177)
                  ·
                    refine ⟨2044734737473373634286633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2726312983297831512382177 2044734737473373634286633)
                    ·
                      refine ⟨1533551053105030225714975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2044734737473373634286633 1533551053105030225714975)
                      ·
                        rfl

theorem cell23_2986580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_2986580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986580 prefixEnd_2986580 := by exact prefixLift 2986580
  have htrace : WordTrace (prefixWord ++ tailWord_2986580) baseStart_2986580 baseEnd_2986580 := by
    simpa [prefixWord, tailWord_2986580, baseEnd_2986580] using wordTrace_append hprefix tailTrace_2986580
  have hstable : (prefixWord ++ tailWord_2986580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986580).length < 2 ^ (prefixWord ++ tailWord_2986580).sum := by decide
  have hdescent : baseEnd_2986580 < baseStart_2986580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986597 : List Nat := [1, 3, 1, 3, 4, 1, 3, 1, 2, 2, 2]
def baseStart_2986597 : Nat := 118140960795 + 2986597 * 2 ^ 59
def prefixEnd_2986597 : Nat := 4983230072969 + 3 ^ 40 * 2986597 * 2
def baseEnd_2986597 : Nat := 1533559782276156659202397

theorem tailTrace_2986597 : CollatzResearch.WordTrace tailWord_2986597 prefixEnd_2986597 1533559782276156659202397 := by
  unfold tailWord_2986597
  simp only [CollatzResearch.WordTrace]
  refine ⟨108930141561076614003950045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72620094374051076002633363 108930141561076614003950045)
  ·
    refine ⟨40848803085403730251481267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108930141561076614003950045 40848803085403730251481267)
    ·
      refine ⟨61273204628105595377221901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40848803085403730251481267 61273204628105595377221901)
      ·
        refine ⟨22977451735539598266458213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61273204628105595377221901 22977451735539598266458213)
        ·
          refine ⟨4308272200413674674960915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22977451735539598266458213 4308272200413674674960915)
          ·
            refine ⟨6462408300620512012441373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4308272200413674674960915 6462408300620512012441373)
            ·
              refine ⟨2423403112732692004665515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6462408300620512012441373 2423403112732692004665515)
              ·
                refine ⟨3635104669099038006998273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2423403112732692004665515 3635104669099038006998273)
                ·
                  refine ⟨2726328501824278505248705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3635104669099038006998273 2726328501824278505248705)
                  ·
                    refine ⟨2044746376368208878936529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2726328501824278505248705 2044746376368208878936529)
                    ·
                      refine ⟨1533559782276156659202397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2044746376368208878936529 1533559782276156659202397)
                      ·
                        rfl

theorem cell23_2986597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_2986597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986597 prefixEnd_2986597 := by exact prefixLift 2986597
  have htrace : WordTrace (prefixWord ++ tailWord_2986597) baseStart_2986597 baseEnd_2986597 := by
    simpa [prefixWord, tailWord_2986597, baseEnd_2986597] using wordTrace_append hprefix tailTrace_2986597
  have hstable : (prefixWord ++ tailWord_2986597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986597).length < 2 ^ (prefixWord ++ tailWord_2986597).sum := by decide
  have hdescent : baseEnd_2986597 < baseStart_2986597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986636 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 2, 4, 2]
def baseStart_2986636 : Nat := 118140960795 + 2986636 * 2 ^ 59
def prefixEnd_2986636 : Nat := 4983230072969 + 3 ^ 40 * 2986636 * 2
def baseEnd_2986636 : Nat := 1533579808021682006614717

theorem tailTrace_2986636 : CollatzResearch.WordTrace tailWord_2986636 prefixEnd_2986636 1533579808021682006614717 := by
  unfold tailWord_2986636
  simp only [CollatzResearch.WordTrace]
  refine ⟨54465782003967661832309881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72621042671956882443079841 54465782003967661832309881)
  ·
    refine ⟨40849336502975746374232411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54465782003967661832309881 40849336502975746374232411)
    ·
      refine ⟨61274004754463619561348617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40849336502975746374232411 61274004754463619561348617)
      ·
        refine ⟨45955503565847714671011463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61274004754463619561348617 45955503565847714671011463)
        ·
          refine ⟨68933255348771572006517195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45955503565847714671011463 68933255348771572006517195)
          ·
            refine ⟨103399883023157358009775793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68933255348771572006517195 103399883023157358009775793)
            ·
              refine ⟨77549912267368018507331845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103399883023157358009775793 77549912267368018507331845)
              ·
                refine ⟨14540608550131503470124721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77549912267368018507331845 14540608550131503470124721)
                ·
                  refine ⟨10905456412598627602593541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14540608550131503470124721 10905456412598627602593541)
                  ·
                    refine ⟨2044773077362242675486289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10905456412598627602593541 2044773077362242675486289)
                    ·
                      refine ⟨1533579808021682006614717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2044773077362242675486289 1533579808021682006614717)
                      ·
                        rfl

theorem cell23_2986636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_2986636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986636 prefixEnd_2986636 := by exact prefixLift 2986636
  have htrace : WordTrace (prefixWord ++ tailWord_2986636) baseStart_2986636 baseEnd_2986636 := by
    simpa [prefixWord, tailWord_2986636, baseEnd_2986636] using wordTrace_append hprefix tailTrace_2986636
  have hstable : (prefixWord ++ tailWord_2986636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986636).length < 2 ^ (prefixWord ++ tailWord_2986636).sum := by decide
  have hdescent : baseEnd_2986636 < baseStart_2986636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986670 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2986670 : Nat := 118140960795 + 2986670 * 2 ^ 59
def prefixEnd_2986670 : Nat := 4983230072969 + 3 ^ 40 * 2986670 * 2
def baseEnd_2986670 : Nat := 1533597266363934873589561

theorem tailTrace_2986670 : CollatzResearch.WordTrace tailWord_2986670 prefixEnd_2986670 1533597266363934873589561 := by
  unfold tailWord_2986670
  simp only [CollatzResearch.WordTrace]
  refine ⟨13616600511226518433919683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72621869393208098314238309 13616600511226518433919683)
  ·
    refine ⟨20424900766839777650879525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13616600511226518433919683 20424900766839777650879525)
    ·
      refine ⟨3829668893782458309539911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20424900766839777650879525 3829668893782458309539911)
      ·
        refine ⟨5744503340673687464309867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3829668893782458309539911 5744503340673687464309867)
        ·
          refine ⟨8616755011010531196464801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5744503340673687464309867 8616755011010531196464801)
          ·
            refine ⟨6462566258257898397348601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8616755011010531196464801 6462566258257898397348601)
            ·
              refine ⟨4846924693693423798011451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6462566258257898397348601 4846924693693423798011451)
              ·
                refine ⟨7270387040540135697017177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4846924693693423798011451 7270387040540135697017177)
                ·
                  refine ⟨5452790280405101772762883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7270387040540135697017177 5452790280405101772762883)
                  ·
                    refine ⟨8179185420607652659144325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5452790280405101772762883 8179185420607652659144325)
                    ·
                      refine ⟨1533597266363934873589561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8179185420607652659144325 1533597266363934873589561)
                      ·
                        rfl

theorem cell23_2986670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2986670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986670 prefixEnd_2986670 := by exact prefixLift 2986670
  have htrace : WordTrace (prefixWord ++ tailWord_2986670) baseStart_2986670 baseEnd_2986670 := by
    simpa [prefixWord, tailWord_2986670, baseEnd_2986670] using wordTrace_append hprefix tailTrace_2986670
  have hstable : (prefixWord ++ tailWord_2986670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986670).length < 2 ^ (prefixWord ++ tailWord_2986670).sum := by decide
  have hdescent : baseEnd_2986670 < baseStart_2986670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986736 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 4, 4]
def baseStart_2986736 : Nat := 118140960795 + 2986736 * 2 ^ 59
def prefixEnd_2986736 : Nat := 4983230072969 + 3 ^ 40 * 2986736 * 2
def baseEnd_2986736 : Nat := 511210385362377205121419

theorem tailTrace_2986736 : CollatzResearch.WordTrace tailWord_2986736 prefixEnd_2986736 511210385362377205121419 := by
  unfold tailWord_2986736
  simp only [CollatzResearch.WordTrace]
  refine ⟨54467605653786520371630031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72623474205048693828840041 54467605653786520371630031)
  ·
    refine ⟨81701408480679780557445047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54467605653786520371630031 81701408480679780557445047)
    ·
      refine ⟨122552112721019670836167571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81701408480679780557445047 122552112721019670836167571)
      ·
        refine ⟨183828169081529506254251357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122552112721019670836167571 183828169081529506254251357)
        ·
          refine ⟨68935563405573564845344259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183828169081529506254251357 68935563405573564845344259)
          ·
            refine ⟨103403345108360347268016389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68935563405573564845344259 103403345108360347268016389)
            ·
              refine ⟨19388127207817565112753073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103403345108360347268016389 19388127207817565112753073)
              ·
                refine ⟨14541095405863173834564805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19388127207817565112753073 14541095405863173834564805)
                ·
                  refine ⟨2726455388599345093980901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14541095405863173834564805 2726455388599345093980901)
                  ·
                    refine ⟨511210385362377205121419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2726455388599345093980901 511210385362377205121419)
                    ·
                      rfl

theorem cell23_2986736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 4, 4].length) (baseStart_2986736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986736 prefixEnd_2986736 := by exact prefixLift 2986736
  have htrace : WordTrace (prefixWord ++ tailWord_2986736) baseStart_2986736 baseEnd_2986736 := by
    simpa [prefixWord, tailWord_2986736, baseEnd_2986736] using wordTrace_append hprefix tailTrace_2986736
  have hstable : (prefixWord ++ tailWord_2986736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986736).length < 2 ^ (prefixWord ++ tailWord_2986736).sum := by decide
  have hdescent : baseEnd_2986736 < baseStart_2986736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986739 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 6]
def baseStart_2986739 : Nat := 118140960795 + 2986739 * 2 ^ 59
def prefixEnd_2986739 : Nat := 4983230072969 + 3 ^ 40 * 2986739 * 2
def baseEnd_2986739 : Nat := 1533632696529095103626743

theorem tailTrace_2986739 : CollatzResearch.WordTrace tailWord_2986739 prefixEnd_2986739 1533632696529095103626743 := by
  unfold tailWord_2986739
  simp only [CollatzResearch.WordTrace]
  refine ⟨108935320726562172255619271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72623547151041448170412847 108935320726562172255619271)
  ·
    refine ⟨163402981089843258383428907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108935320726562172255619271 163402981089843258383428907)
    ·
      refine ⟨245104471634764887575143361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163402981089843258383428907 245104471634764887575143361)
      ·
        refine ⟨183828353726073665681357521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245104471634764887575143361 183828353726073665681357521)
        ·
          refine ⟨137871265294555249261018141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183828353726073665681357521 137871265294555249261018141)
          ·
            refine ⟨51701724485458218472881803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137871265294555249261018141 51701724485458218472881803)
            ·
              refine ⟨77552586728187327709322705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51701724485458218472881803 77552586728187327709322705)
              ·
                refine ⟨58164440046140495781992029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77552586728187327709322705 58164440046140495781992029)
                ·
                  refine ⟨21811665017302685918247011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58164440046140495781992029 21811665017302685918247011)
                  ·
                    refine ⟨32717497525954028877370517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21811665017302685918247011 32717497525954028877370517)
                    ·
                      refine ⟨1533632696529095103626743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32717497525954028877370517 1533632696529095103626743)
                      ·
                        rfl

theorem cell23_2986739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_2986739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986739 prefixEnd_2986739 := by exact prefixLift 2986739
  have htrace : WordTrace (prefixWord ++ tailWord_2986739) baseStart_2986739 baseEnd_2986739 := by
    simpa [prefixWord, tailWord_2986739, baseEnd_2986739] using wordTrace_append hprefix tailTrace_2986739
  have hstable : (prefixWord ++ tailWord_2986739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986739).length < 2 ^ (prefixWord ++ tailWord_2986739).sum := by decide
  have hdescent : baseEnd_2986739 < baseStart_2986739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986743 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 7, 2, 2]
def baseStart_2986743 : Nat := 118140960795 + 2986743 * 2 ^ 59
def prefixEnd_2986743 : Nat := 4983230072969 + 3 ^ 40 * 2986743 * 2
def baseEnd_2986743 : Nat := 1533634750451713087976725

theorem tailTrace_2986743 : CollatzResearch.WordTrace tailWord_2986743 prefixEnd_2986743 1533634750451713087976725 := by
  unfold tailWord_2986743
  simp only [CollatzResearch.WordTrace]
  refine ⟨108935466618547680938764883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72623644412365120625843255 108935466618547680938764883)
  ·
    refine ⟨163403199927821521408147325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108935466618547680938764883 163403199927821521408147325)
    ·
      refine ⟨61276199972933070528055247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163403199927821521408147325 61276199972933070528055247)
      ·
        refine ⟨91914299959399605792082871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61276199972933070528055247 91914299959399605792082871)
        ·
          refine ⟨137871449939099408688124307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91914299959399605792082871 137871449939099408688124307)
          ·
            refine ⟨206807174908649113032186461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137871449939099408688124307 206807174908649113032186461)
            ·
              refine ⟨77552690590743417387069923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206807174908649113032186461 77552690590743417387069923)
              ·
                refine ⟨116329035886115126080604885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77552690590743417387069923 116329035886115126080604885)
                ·
                  refine ⟨2726461778580823267514177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 116329035886115126080604885 2726461778580823267514177)
                  ·
                    refine ⟨2044846333935617450635633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2726461778580823267514177 2044846333935617450635633)
                    ·
                      refine ⟨1533634750451713087976725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2044846333935617450635633 1533634750451713087976725)
                      ·
                        rfl

theorem cell23_2986743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 2, 2].length) (baseStart_2986743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986743 prefixEnd_2986743 := by exact prefixLift 2986743
  have htrace : WordTrace (prefixWord ++ tailWord_2986743) baseStart_2986743 baseEnd_2986743 := by
    simpa [prefixWord, tailWord_2986743, baseEnd_2986743] using wordTrace_append hprefix tailTrace_2986743
  have hstable : (prefixWord ++ tailWord_2986743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986743).length < 2 ^ (prefixWord ++ tailWord_2986743).sum := by decide
  have hdescent : baseEnd_2986743 < baseStart_2986743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986749 : List Nat := [1, 4, 1, 1, 1, 1, 14]
def baseStart_2986749 : Nat := 118140960795 + 2986749 * 2 ^ 59
def prefixEnd_2986749 : Nat := 4983230072969 + 3 ^ 40 * 2986749 * 2
def baseEnd_2986749 : Nat := 18933800386859753882737

theorem tailTrace_2986749 : CollatzResearch.WordTrace tailWord_2986749 prefixEnd_2986749 18933800386859753882737 := by
  unfold tailWord_2986749
  simp only [CollatzResearch.WordTrace]
  refine ⟨108935685456525943963483301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72623790304350629308988867 108935685456525943963483301)
  ·
    refine ⟨20425441023098614493153119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108935685456525943963483301 20425441023098614493153119)
    ·
      refine ⟨30638161534647921739729679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20425441023098614493153119 30638161534647921739729679)
      ·
        refine ⟨45957242301971882609594519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30638161534647921739729679 45957242301971882609594519)
        ·
          refine ⟨68935863452957823914391779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45957242301971882609594519 68935863452957823914391779)
          ·
            refine ⟨103403795179436735871587669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68935863452957823914391779 103403795179436735871587669)
            ·
              refine ⟨18933800386859753882737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 103403795179436735871587669 18933800386859753882737)
              ·
                rfl

theorem cell23_2986749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 14].length) (baseStart_2986749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986749 prefixEnd_2986749 := by exact prefixLift 2986749
  have htrace : WordTrace (prefixWord ++ tailWord_2986749) baseStart_2986749 baseEnd_2986749 := by
    simpa [prefixWord, tailWord_2986749, baseEnd_2986749] using wordTrace_append hprefix tailTrace_2986749
  have hstable : (prefixWord ++ tailWord_2986749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986749).length < 2 ^ (prefixWord ++ tailWord_2986749).sum := by decide
  have hdescent : baseEnd_2986749 < baseStart_2986749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986756 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_2986756 : Nat := 118140960795 + 2986756 * 2 ^ 59
def prefixEnd_2986756 : Nat := 4983230072969 + 3 ^ 40 * 2986756 * 2
def baseEnd_2986756 : Nat := 1533641425700221537114165

theorem tailTrace_2986756 : CollatzResearch.WordTrace tailWord_2986756 prefixEnd_2986756 1533641425700221537114165 := by
  unfold tailWord_2986756
  simp only [CollatzResearch.WordTrace]
  refine ⟨54467970383750292079494061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72623960511667056105992081 54467970383750292079494061)
  ·
    refine ⟨20425488893906359529810273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54467970383750292079494061 20425488893906359529810273)
    ·
      refine ⟨15319116670429769647357705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20425488893906359529810273 15319116670429769647357705)
      ·
        refine ⟨11489337502822327235518279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15319116670429769647357705 11489337502822327235518279)
        ·
          refine ⟨17234006254233490853277419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11489337502822327235518279 17234006254233490853277419)
          ·
            refine ⟨25851009381350236279916129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17234006254233490853277419 25851009381350236279916129)
            ·
              refine ⟨19388257036012677209937097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25851009381350236279916129 19388257036012677209937097)
              ·
                refine ⟨14541192777009507907452823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19388257036012677209937097 14541192777009507907452823)
                ·
                  refine ⟨21811789165514261861179235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14541192777009507907452823 21811789165514261861179235)
                  ·
                    refine ⟨32717683748271392791768853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21811789165514261861179235 32717683748271392791768853)
                    ·
                      refine ⟨1533641425700221537114165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32717683748271392791768853 1533641425700221537114165)
                      ·
                        rfl

theorem cell23_2986756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_2986756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986756 prefixEnd_2986756 := by exact prefixLift 2986756
  have htrace : WordTrace (prefixWord ++ tailWord_2986756) baseStart_2986756 baseEnd_2986756 := by
    simpa [prefixWord, tailWord_2986756, baseEnd_2986756] using wordTrace_append hprefix tailTrace_2986756
  have hstable : (prefixWord ++ tailWord_2986756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986756).length < 2 ^ (prefixWord ++ tailWord_2986756).sum := by decide
  have hdescent : baseEnd_2986756 < baseStart_2986756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986760 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 3, 2, 2]
def baseStart_2986760 : Nat := 118140960795 + 2986760 * 2 ^ 59
def prefixEnd_2986760 : Nat := 4983230072969 + 3 ^ 40 * 2986760 * 2
def baseEnd_2986760 : Nat := 1533643479622839521464147

theorem tailTrace_2986760 : CollatzResearch.WordTrace tailWord_2986760 prefixEnd_2986760 1533643479622839521464147 := by
  unfold tailWord_2986760
  simp only [CollatzResearch.WordTrace]
  refine ⟨54468043329743046421066867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72624057772990728561422489 54468043329743046421066867)
  ·
    refine ⟨81702064994614569631600301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54468043329743046421066867 81702064994614569631600301)
    ·
      refine ⟨30638274372980463611850113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81702064994614569631600301 30638274372980463611850113)
      ·
        refine ⟨22978705779735347708887585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30638274372980463611850113 22978705779735347708887585)
        ·
          refine ⟨17234029334801510781665689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22978705779735347708887585 17234029334801510781665689)
          ·
            refine ⟨12925522001101133086249267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17234029334801510781665689 12925522001101133086249267)
            ·
              refine ⟨19388283001651699629373901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12925522001101133086249267 19388283001651699629373901)
              ·
                refine ⟨7270606125619387361015213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19388283001651699629373901 7270606125619387361015213)
                ·
                  refine ⟨2726477297107270260380705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7270606125619387361015213 2726477297107270260380705)
                  ·
                    refine ⟨2044857972830452695285529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2726477297107270260380705 2044857972830452695285529)
                    ·
                      refine ⟨1533643479622839521464147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2044857972830452695285529 1533643479622839521464147)
                      ·
                        rfl

theorem cell23_2986760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_2986760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986760 prefixEnd_2986760 := by exact prefixLift 2986760
  have htrace : WordTrace (prefixWord ++ tailWord_2986760) baseStart_2986760 baseEnd_2986760 := by
    simpa [prefixWord, tailWord_2986760, baseEnd_2986760] using wordTrace_append hprefix tailTrace_2986760
  have hstable : (prefixWord ++ tailWord_2986760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986760).length < 2 ^ (prefixWord ++ tailWord_2986760).sum := by decide
  have hdescent : baseEnd_2986760 < baseStart_2986760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986780 : List Nat := [2, 2, 3, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_2986780 : Nat := 118140960795 + 2986780 * 2 ^ 59
def prefixEnd_2986780 : Nat := 4983230072969 + 3 ^ 40 * 2986780 * 2
def baseEnd_2986780 : Nat := 1533653749235929443214055

theorem tailTrace_2986780 : CollatzResearch.WordTrace tailWord_2986780 prefixEnd_2986780 1533653749235929443214055 := by
  unfold tailWord_2986780
  simp only [CollatzResearch.WordTrace]
  refine ⟨54468408059706818128930897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72624544079609090838574529 54468408059706818128930897)
  ·
    refine ⟨40851306044780113596698173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54468408059706818128930897 40851306044780113596698173)
    ·
      refine ⟨15319239766792542598761815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40851306044780113596698173 15319239766792542598761815)
      ·
        refine ⟨22978859650188813898142723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15319239766792542598761815 22978859650188813898142723)
        ·
          refine ⟨34468289475283220847214085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22978859650188813898142723 34468289475283220847214085)
          ·
            refine ⟨6462804276615603908852641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34468289475283220847214085 6462804276615603908852641)
            ·
              refine ⟨4847103207461702931639481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6462804276615603908852641 4847103207461702931639481)
              ·
                refine ⟨3635327405596277198729611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4847103207461702931639481 3635327405596277198729611)
                ·
                  refine ⟨5452991108394415798094417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3635327405596277198729611 5452991108394415798094417)
                  ·
                    refine ⟨4089743331295811848570813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5452991108394415798094417 4089743331295811848570813)
                    ·
                      refine ⟨1533653749235929443214055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4089743331295811848570813 1533653749235929443214055)
                      ·
                        rfl

theorem cell23_2986780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_2986780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986780 prefixEnd_2986780 := by exact prefixLift 2986780
  have htrace : WordTrace (prefixWord ++ tailWord_2986780) baseStart_2986780 baseEnd_2986780 := by
    simpa [prefixWord, tailWord_2986780, baseEnd_2986780] using wordTrace_append hprefix tailTrace_2986780
  have hstable : (prefixWord ++ tailWord_2986780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986780).length < 2 ^ (prefixWord ++ tailWord_2986780).sum := by decide
  have hdescent : baseEnd_2986780 < baseStart_2986780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986783 : List Nat := [1, 1, 2, 4, 2, 4, 2, 7]
def baseStart_2986783 : Nat := 118140960795 + 2986783 * 2 ^ 59
def prefixEnd_2986783 : Nat := 4983230072969 + 3 ^ 40 * 2986783 * 2
def baseEnd_2986783 : Nat := 56802047765847886350983

theorem tailTrace_2986783 : CollatzResearch.WordTrace tailWord_2986783 prefixEnd_2986783 56802047765847886350983 := by
  unfold tailWord_2986783
  simp only [CollatzResearch.WordTrace]
  refine ⟨108936925538402767770221003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72624617025601845180147335 108936925538402767770221003)
  ·
    refine ⟨163405388307604151655331505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108936925538402767770221003 163405388307604151655331505)
    ·
      refine ⟨122554041230703113741498629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163405388307604151655331505 122554041230703113741498629)
      ·
        refine ⟨22978882730756833826530993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122554041230703113741498629 22978882730756833826530993)
        ·
          refine ⟨17234162048067625369898245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22978882730756833826530993 17234162048067625369898245)
          ·
            refine ⟨3231405384012679756855921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17234162048067625369898245 3231405384012679756855921)
            ·
              refine ⟨2423554038009509817641941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3231405384012679756855921 2423554038009509817641941)
              ·
                refine ⟨56802047765847886350983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2423554038009509817641941 56802047765847886350983)
                ·
                  rfl

theorem cell23_2986783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 7].length) (baseStart_2986783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986783 prefixEnd_2986783 := by exact prefixLift 2986783
  have htrace : WordTrace (prefixWord ++ tailWord_2986783) baseStart_2986783 baseEnd_2986783 := by
    simpa [prefixWord, tailWord_2986783, baseEnd_2986783] using wordTrace_append hprefix tailTrace_2986783
  have hstable : (prefixWord ++ tailWord_2986783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986783).length < 2 ^ (prefixWord ++ tailWord_2986783).sum := by decide
  have hdescent : baseEnd_2986783 < baseStart_2986783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986797 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2986797 : Nat := 118140960795 + 2986797 * 2 ^ 59
def prefixEnd_2986797 : Nat := 4983230072969 + 3 ^ 40 * 2986797 * 2
def baseEnd_2986797 : Nat := 1533662478407055876701477

theorem tailTrace_2986797 : CollatzResearch.WordTrace tailWord_2986797 prefixEnd_2986797 1533662478407055876701477 := by
  unfold tailWord_2986797
  simp only [CollatzResearch.WordTrace]
  refine ⟨108937436160352048161230645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72624957440234698774153763 108937436160352048161230645)
  ·
    refine ⟨10212884640033004515115373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108937436160352048161230645 10212884640033004515115373)
    ·
      refine ⟨3829831740012376693168265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10212884640033004515115373 3829831740012376693168265)
      ·
        refine ⟨2872373805009282519876199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3829831740012376693168265 2872373805009282519876199)
        ·
          refine ⟨4308560707513923779814299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2872373805009282519876199 4308560707513923779814299)
          ·
            refine ⟨6462841061270885669721449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4308560707513923779814299 6462841061270885669721449)
            ·
              refine ⟨4847130795953164252291087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6462841061270885669721449 4847130795953164252291087)
              ·
                refine ⟨7270696193929746378436631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4847130795953164252291087 7270696193929746378436631)
                ·
                  refine ⟨10906044290894619567654947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7270696193929746378436631 10906044290894619567654947)
                  ·
                    refine ⟨16359066436341929351482421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10906044290894619567654947 16359066436341929351482421)
                    ·
                      refine ⟨1533662478407055876701477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16359066436341929351482421 1533662478407055876701477)
                      ·
                        rfl

theorem cell23_2986797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2986797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986797 prefixEnd_2986797 := by exact prefixLift 2986797
  have htrace : WordTrace (prefixWord ++ tailWord_2986797) baseStart_2986797 baseEnd_2986797 := by
    simpa [prefixWord, tailWord_2986797, baseEnd_2986797] using wordTrace_append hprefix tailTrace_2986797
  have hstable : (prefixWord ++ tailWord_2986797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986797).length < 2 ^ (prefixWord ++ tailWord_2986797).sum := by decide
  have hdescent : baseEnd_2986797 < baseStart_2986797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986866 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_2986866 : Nat := 118140960795 + 2986866 * 2 ^ 59
def prefixEnd_2986866 : Nat := 4983230072969 + 3 ^ 40 * 2986866 * 2
def baseEnd_2986866 : Nat := 1533697908572216106738659

theorem tailTrace_2986866 : CollatzResearch.WordTrace tailWord_2986866 prefixEnd_2986866 1533697908572216106738659 := by
  unfold tailWord_2986866
  simp only [CollatzResearch.WordTrace]
  refine ⟨27234988199275518236373113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72626635198068048630328301 27234988199275518236373113)
  ·
    refine ⟨20426241149456638677279835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27234988199275518236373113 20426241149456638677279835)
    ·
      refine ⟨30639361724184958015919753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20426241149456638677279835 30639361724184958015919753)
      ·
        refine ⟨22979521293138718511939815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30639361724184958015919753 22979521293138718511939815)
        ·
          refine ⟨34469281939708077767909723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22979521293138718511939815 34469281939708077767909723)
          ·
            refine ⟨51703922909562116651864585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34469281939708077767909723 51703922909562116651864585)
            ·
              refine ⟨38777942182171587488898439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51703922909562116651864585 38777942182171587488898439)
              ·
                refine ⟨58166913273257381233347659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38777942182171587488898439 58166913273257381233347659)
                ·
                  refine ⟨87250369909886071850021489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58166913273257381233347659 87250369909886071850021489)
                  ·
                    refine ⟨65437777432414553887516117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87250369909886071850021489 65437777432414553887516117)
                    ·
                      refine ⟨1533697908572216106738659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65437777432414553887516117 1533697908572216106738659)
                      ·
                        rfl

theorem cell23_2986866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_2986866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986866 prefixEnd_2986866 := by exact prefixLift 2986866
  have htrace : WordTrace (prefixWord ++ tailWord_2986866) baseStart_2986866 baseEnd_2986866 := by
    simpa [prefixWord, tailWord_2986866, baseEnd_2986866] using wordTrace_append hprefix tailTrace_2986866
  have hstable : (prefixWord ++ tailWord_2986866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986866).length < 2 ^ (prefixWord ++ tailWord_2986866).sum := by decide
  have hdescent : baseEnd_2986866 < baseStart_2986866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986870 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_2986870 : Nat := 118140960795 + 2986870 * 2 ^ 59
def prefixEnd_2986870 : Nat := 4983230072969 + 3 ^ 40 * 2986870 * 2
def baseEnd_2986870 : Nat := 1533699962494834091088641

theorem tailTrace_2986870 : CollatzResearch.WordTrace tailWord_2986870 prefixEnd_2986870 1533699962494834091088641 := by
  unfold tailWord_2986870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6808756168067973851789879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72626732459391721085758709 6808756168067973851789879)
  ·
    refine ⟨10213134252101960777684819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6808756168067973851789879 10213134252101960777684819)
    ·
      refine ⟨15319701378152941166527229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10213134252101960777684819 15319701378152941166527229)
      ·
        refine ⟨5744888016807352937447711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15319701378152941166527229 5744888016807352937447711)
        ·
          refine ⟨8617332025211029406171567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5744888016807352937447711 8617332025211029406171567)
          ·
            refine ⟨12925998037816544109257351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8617332025211029406171567 12925998037816544109257351)
            ·
              refine ⟨19388997056724816163886027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12925998037816544109257351 19388997056724816163886027)
              ·
                refine ⟨29083495585087224245829041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19388997056724816163886027 29083495585087224245829041)
                ·
                  refine ⟨21812621688815418184371781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29083495585087224245829041 21812621688815418184371781)
                  ·
                    refine ⟨4089866566652890909569709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21812621688815418184371781 4089866566652890909569709)
                    ·
                      refine ⟨1533699962494834091088641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4089866566652890909569709 1533699962494834091088641)
                      ·
                        rfl

theorem cell23_2986870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_2986870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986870 prefixEnd_2986870 := by exact prefixLift 2986870
  have htrace : WordTrace (prefixWord ++ tailWord_2986870) baseStart_2986870 baseEnd_2986870 := by
    simpa [prefixWord, tailWord_2986870, baseEnd_2986870] using wordTrace_append hprefix tailTrace_2986870
  have hstable : (prefixWord ++ tailWord_2986870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986870).length < 2 ^ (prefixWord ++ tailWord_2986870).sum := by decide
  have hdescent : baseEnd_2986870 < baseStart_2986870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986883 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 3]
def baseStart_2986883 : Nat := 118140960795 + 2986883 * 2 ^ 59
def prefixEnd_2986883 : Nat := 4983230072969 + 3 ^ 40 * 2986883 * 2
def baseEnd_2986883 : Nat := 1533706637743342540226081

theorem tailTrace_2986883 : CollatzResearch.WordTrace tailWord_2986883 prefixEnd_2986883 1533706637743342540226081 := by
  unfold tailWord_2986883
  simp only [CollatzResearch.WordTrace]
  refine ⟨108940572838040484848861303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72627048558693656565907535 108940572838040484848861303)
  ·
    refine ⟨163410859257060727273291955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108940572838040484848861303 163410859257060727273291955)
    ·
      refine ⟨245116288885591090909937933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163410859257060727273291955 245116288885591090909937933)
      ·
        refine ⟨91918608332096659091226725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245116288885591090909937933 91918608332096659091226725)
        ·
          refine ⟨17234739062268123579605011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91918608332096659091226725 17234739062268123579605011)
          ·
            refine ⟨25852108593402185369407517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17234739062268123579605011 25852108593402185369407517)
            ·
              refine ⟨9694540722525819513527819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25852108593402185369407517 9694540722525819513527819)
              ·
                refine ⟨14541811083788729270291729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9694540722525819513527819 14541811083788729270291729)
                ·
                  refine ⟨10906358312841546952718797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14541811083788729270291729 10906358312841546952718797)
                  ·
                    refine ⟨4089884367315580107269549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10906358312841546952718797 4089884367315580107269549)
                    ·
                      refine ⟨1533706637743342540226081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4089884367315580107269549 1533706637743342540226081)
                      ·
                        rfl

theorem cell23_2986883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_2986883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986883 prefixEnd_2986883 := by exact prefixLift 2986883
  have htrace : WordTrace (prefixWord ++ tailWord_2986883) baseStart_2986883 baseEnd_2986883 := by
    simpa [prefixWord, tailWord_2986883, baseEnd_2986883] using wordTrace_append hprefix tailTrace_2986883
  have hstable : (prefixWord ++ tailWord_2986883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986883).length < 2 ^ (prefixWord ++ tailWord_2986883).sum := by decide
  have hdescent : baseEnd_2986883 < baseStart_2986883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986923 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 3, 6, 2]
def baseStart_2986923 : Nat := 118140960795 + 2986923 * 2 ^ 59
def prefixEnd_2986923 : Nat := 4983230072969 + 3 ^ 40 * 2986923 * 2
def baseEnd_2986923 : Nat := 1533727176969522383725897

theorem tailTrace_2986923 : CollatzResearch.WordTrace tailWord_2986923 prefixEnd_2986923 1533727176969522383725897 := by
  unfold tailWord_2986923
  simp only [CollatzResearch.WordTrace]
  refine ⟨108942031757895571680317423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72628021171930381120211615 108942031757895571680317423)
  ·
    refine ⟨163413047636843357520476135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108942031757895571680317423 163413047636843357520476135)
    ·
      refine ⟨245119571455265036280714203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163413047636843357520476135 245119571455265036280714203)
      ·
        refine ⟨367679357182897554421071305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245119571455265036280714203 367679357182897554421071305)
        ·
          refine ⟨275759517887173165815803479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367679357182897554421071305 275759517887173165815803479)
          ·
            refine ⟨413639276830759748723705219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275759517887173165815803479 413639276830759748723705219)
            ·
              refine ⟨620458915246139623085557829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413639276830759748723705219 620458915246139623085557829)
              ·
                refine ⟨116336046608651179328542093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 620458915246139623085557829 116336046608651179328542093)
                ·
                  refine ⟨43626017478244192248203285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116336046608651179328542093 43626017478244192248203285)
                  ·
                    refine ⟨2044969569292696511634529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43626017478244192248203285 2044969569292696511634529)
                    ·
                      refine ⟨1533727176969522383725897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2044969569292696511634529 1533727176969522383725897)
                      ·
                        rfl

theorem cell23_2986923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 6, 2].length) (baseStart_2986923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986923 prefixEnd_2986923 := by exact prefixLift 2986923
  have htrace : WordTrace (prefixWord ++ tailWord_2986923) baseStart_2986923 baseEnd_2986923 := by
    simpa [prefixWord, tailWord_2986923, baseEnd_2986923] using wordTrace_append hprefix tailTrace_2986923
  have hstable : (prefixWord ++ tailWord_2986923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986923).length < 2 ^ (prefixWord ++ tailWord_2986923).sum := by decide
  have hdescent : baseEnd_2986923 < baseStart_2986923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2986943 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 3]
def baseStart_2986943 : Nat := 118140960795 + 2986943 * 2 ^ 59
def prefixEnd_2986943 : Nat := 4983230072969 + 3 ^ 40 * 2986943 * 2
def baseEnd_2986943 : Nat := 1533737446582612305475805

theorem tailTrace_2986943 : CollatzResearch.WordTrace tailWord_2986943 prefixEnd_2986943 1533737446582612305475805 := by
  unfold tailWord_2986943
  simp only [CollatzResearch.WordTrace]
  refine ⟨108942761217823115096045483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72628507478548743397363655 108942761217823115096045483)
  ·
    refine ⟨163414141826734672644068225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108942761217823115096045483 163414141826734672644068225)
    ·
      refine ⟨122560606370051004483051169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163414141826734672644068225 122560606370051004483051169)
      ·
        refine ⟨91920454777538253362288377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122560606370051004483051169 91920454777538253362288377)
        ·
          refine ⟨68940341083153690021716283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91920454777538253362288377 68940341083153690021716283)
          ·
            refine ⟨103410511624730535032574425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68940341083153690021716283 103410511624730535032574425)
            ·
              refine ⟨77557883718547901274430819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103410511624730535032574425 77557883718547901274430819)
              ·
                refine ⟨116336825577821851911646229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77557883718547901274430819 116336825577821851911646229)
                ·
                  refine ⟨5453288698960399308358417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116336825577821851911646229 5453288698960399308358417)
                  ·
                    refine ⟨4089966524220299481268813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5453288698960399308358417 4089966524220299481268813)
                    ·
                      refine ⟨1533737446582612305475805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4089966524220299481268813 1533737446582612305475805)
                      ·
                        rfl

theorem cell23_2986943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_2986943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2986943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2986943 prefixEnd_2986943 := by exact prefixLift 2986943
  have htrace : WordTrace (prefixWord ++ tailWord_2986943) baseStart_2986943 baseEnd_2986943 := by
    simpa [prefixWord, tailWord_2986943, baseEnd_2986943] using wordTrace_append hprefix tailTrace_2986943
  have hstable : (prefixWord ++ tailWord_2986943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2986943).length < 2 ^ (prefixWord ++ tailWord_2986943).sum := by decide
  have hdescent : baseEnd_2986943 < baseStart_2986943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2986943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987000 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 6, 3, 2]
def baseStart_2987000 : Nat := 118140960795 + 2987000 * 2 ^ 59
def prefixEnd_2987000 : Nat := 4983230072969 + 3 ^ 40 * 2987000 * 2
def baseEnd_2987000 : Nat := 1533766714979918582463043

theorem tailTrace_2987000 : CollatzResearch.WordTrace tailWord_2987000 prefixEnd_2987000 1533766714979918582463043 := by
  unfold tailWord_2987000
  simp only [CollatzResearch.WordTrace]
  refine ⟨54472420089308306915435227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72629893452411075887246969 54472420089308306915435227)
  ·
    refine ⟨81708630133962460373152841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54472420089308306915435227 81708630133962460373152841)
    ·
      refine ⟨61281472600471845279864631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81708630133962460373152841 61281472600471845279864631)
      ·
        refine ⟨91922208900707767919796947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61281472600471845279864631 91922208900707767919796947)
        ·
          refine ⟨137883313351061651879695421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91922208900707767919796947 137883313351061651879695421)
          ·
            refine ⟨51706242506648119454885783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137883313351061651879695421 51706242506648119454885783)
            ·
              refine ⟨77559363759972179182328675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51706242506648119454885783 77559363759972179182328675)
              ·
                refine ⟨116339045639958268773493013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77559363759972179182328675 116339045639958268773493013)
                ·
                  refine ⟨5453392764373043848757485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116339045639958268773493013 5453392764373043848757485)
                  ·
                    refine ⟨2045022286639891443284057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5453392764373043848757485 2045022286639891443284057)
                    ·
                      refine ⟨1533766714979918582463043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2045022286639891443284057 1533766714979918582463043)
                      ·
                        rfl

theorem cell23_2987000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 6, 3, 2].length) (baseStart_2987000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987000 prefixEnd_2987000 := by exact prefixLift 2987000
  have htrace : WordTrace (prefixWord ++ tailWord_2987000) baseStart_2987000 baseEnd_2987000 := by
    simpa [prefixWord, tailWord_2987000, baseEnd_2987000] using wordTrace_append hprefix tailTrace_2987000
  have hstable : (prefixWord ++ tailWord_2987000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987000).length < 2 ^ (prefixWord ++ tailWord_2987000).sum := by decide
  have hdescent : baseEnd_2987000 < baseStart_2987000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987041 : List Nat := [1, 2, 3, 2, 3, 1, 4, 2, 1, 1, 3]
def baseStart_2987041 : Nat := 118140960795 + 2987041 * 2 ^ 59
def prefixEnd_2987041 : Nat := 4983230072969 + 3 ^ 40 * 2987041 * 2
def baseEnd_2987041 : Nat := 1533787767686752922050355

theorem tailTrace_2987041 : CollatzResearch.WordTrace tailWord_2987041 prefixEnd_2987041 1533787767686752922050355 := by
  unfold tailWord_2987041
  simp only [CollatzResearch.WordTrace]
  refine ⟨108946335571468077833112977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72630890380978718555408651 108946335571468077833112977)
  ·
    refine ⟨81709751678601058374834733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108946335571468077833112977 81709751678601058374834733)
    ·
      refine ⟨30641156879475396890563025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81709751678601058374834733 30641156879475396890563025)
      ·
        refine ⟨22980867659606547667922269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30641156879475396890563025 22980867659606547667922269)
        ·
          refine ⟨8617825372352455375470851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22980867659606547667922269 8617825372352455375470851)
          ·
            refine ⟨12926738058528683063206277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8617825372352455375470851 12926738058528683063206277)
            ·
              refine ⟨2423763385974128074351177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12926738058528683063206277 2423763385974128074351177)
              ·
                refine ⟨1817822539480596055763383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2423763385974128074351177 1817822539480596055763383)
                ·
                  refine ⟨2726733809220894083645075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817822539480596055763383 2726733809220894083645075)
                  ·
                    refine ⟨4090100713831341125467613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2726733809220894083645075 4090100713831341125467613)
                    ·
                      refine ⟨1533787767686752922050355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4090100713831341125467613 1533787767686752922050355)
                      ·
                        rfl

theorem cell23_2987041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_2987041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987041 prefixEnd_2987041 := by exact prefixLift 2987041
  have htrace : WordTrace (prefixWord ++ tailWord_2987041) baseStart_2987041 baseEnd_2987041 := by
    simpa [prefixWord, tailWord_2987041, baseEnd_2987041] using wordTrace_append hprefix tailTrace_2987041
  have hstable : (prefixWord ++ tailWord_2987041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987041).length < 2 ^ (prefixWord ++ tailWord_2987041).sum := by decide
  have hdescent : baseEnd_2987041 < baseStart_2987041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987047 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2987047 : Nat := 118140960795 + 2987047 * 2 ^ 59
def prefixEnd_2987047 : Nat := 4983230072969 + 3 ^ 40 * 2987047 * 2
def baseEnd_2987047 : Nat := 1533790848570679898575327

theorem tailTrace_2987047 : CollatzResearch.WordTrace tailWord_2987047 prefixEnd_2987047 1533790848570679898575327 := by
  unfold tailWord_2987047
  simp only [CollatzResearch.WordTrace]
  refine ⟨108946554409446340857831395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72631036272964227238554263 108946554409446340857831395)
  ·
    refine ⟨163419831614169511286747093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108946554409446340857831395 163419831614169511286747093)
    ·
      refine ⟨3830152303457097920783135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 163419831614169511286747093 3830152303457097920783135)
      ·
        refine ⟨5745228455185646881174703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3830152303457097920783135 5745228455185646881174703)
        ·
          refine ⟨8617842682778470321762055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5745228455185646881174703 8617842682778470321762055)
          ·
            refine ⟨12926764024167705482643083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8617842682778470321762055 12926764024167705482643083)
            ·
              refine ⟨19390146036251558223964625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12926764024167705482643083 19390146036251558223964625)
              ·
                refine ⟨14542609527188668667973469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19390146036251558223964625 14542609527188668667973469)
                ·
                  refine ⟨5453478572695750750490051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14542609527188668667973469 5453478572695750750490051)
                  ·
                    refine ⟨8180217859043626125735077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5453478572695750750490051 8180217859043626125735077)
                    ·
                      refine ⟨1533790848570679898575327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8180217859043626125735077 1533790848570679898575327)
                      ·
                        rfl

theorem cell23_2987047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2987047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987047 prefixEnd_2987047 := by exact prefixLift 2987047
  have htrace : WordTrace (prefixWord ++ tailWord_2987047) baseStart_2987047 baseEnd_2987047 := by
    simpa [prefixWord, tailWord_2987047, baseEnd_2987047] using wordTrace_append hprefix tailTrace_2987047
  have hstable : (prefixWord ++ tailWord_2987047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987047).length < 2 ^ (prefixWord ++ tailWord_2987047).sum := by decide
  have hdescent : baseEnd_2987047 < baseStart_2987047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987064 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 3, 2, 2]
def baseStart_2987064 : Nat := 118140960795 + 2987064 * 2 ^ 59
def prefixEnd_2987064 : Nat := 4983230072969 + 3 ^ 40 * 2987064 * 2
def baseEnd_2987064 : Nat := 1533799577741806332062749

theorem tailTrace_2987064 : CollatzResearch.WordTrace tailWord_2987064 prefixEnd_2987064 1533799577741806332062749 := by
  unfold tailWord_2987064
  simp only [CollatzResearch.WordTrace]
  refine ⟨54473587225192376380600123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72631449633589835174133497 54473587225192376380600123)
  ·
    refine ⟨81710380837788564570900185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54473587225192376380600123 81710380837788564570900185)
    ·
      refine ⟨61282785628341423428175139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81710380837788564570900185 61282785628341423428175139)
      ·
        refine ⟨91924178442512135142262709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61282785628341423428175139 91924178442512135142262709)
        ·
          refine ⟨8617891728985512669587129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91924178442512135142262709 8617891728985512669587129)
          ·
            refine ⟨6463418796739134502190347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8617891728985512669587129 6463418796739134502190347)
            ·
              refine ⟨9695128195108701753285521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6463418796739134502190347 9695128195108701753285521)
              ·
                refine ⟨7271346146331526314964141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9695128195108701753285521 7271346146331526314964141)
                ·
                  refine ⟨2726754804874322368111553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7271346146331526314964141 2726754804874322368111553)
                  ·
                    refine ⟨2045066103655741776083665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2726754804874322368111553 2045066103655741776083665)
                    ·
                      refine ⟨1533799577741806332062749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2045066103655741776083665 1533799577741806332062749)
                      ·
                        rfl

theorem cell23_2987064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 3, 2, 2].length) (baseStart_2987064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987064 prefixEnd_2987064 := by exact prefixLift 2987064
  have htrace : WordTrace (prefixWord ++ tailWord_2987064) baseStart_2987064 baseEnd_2987064 := by
    simpa [prefixWord, tailWord_2987064, baseEnd_2987064] using wordTrace_append hprefix tailTrace_2987064
  have hstable : (prefixWord ++ tailWord_2987064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987064).length < 2 ^ (prefixWord ++ tailWord_2987064).sum := by decide
  have hdescent : baseEnd_2987064 < baseStart_2987064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987080 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 1, 3, 3]
def baseStart_2987080 : Nat := 118140960795 + 2987080 * 2 ^ 59
def prefixEnd_2987080 : Nat := 4983230072969 + 3 ^ 40 * 2987080 * 2
def baseEnd_2987080 : Nat := 1533807793432278269462675

theorem tailTrace_2987080 : CollatzResearch.WordTrace tailWord_2987080 prefixEnd_2987080 1533807793432278269462675 := by
  unfold tailWord_2987080
  simp only [CollatzResearch.WordTrace]
  refine ⟨54473879009163393746891347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72631838678884524995855129 54473879009163393746891347)
  ·
    refine ⟨81710818513745090620337021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54473879009163393746891347 81710818513745090620337021)
    ·
      refine ⟨30641556942654408982626383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81710818513745090620337021 30641556942654408982626383)
      ·
        refine ⟨45962335413981613473939575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30641556942654408982626383 45962335413981613473939575)
        ·
          refine ⟨68943503120972420210909363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45962335413981613473939575 68943503120972420210909363)
          ·
            refine ⟨103415254681458630316364045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68943503120972420210909363 103415254681458630316364045)
            ·
              refine ⟨38780720505546986368636517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103415254681458630316364045 38780720505546986368636517)
              ·
                refine ⟨7271385094790059944119347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38780720505546986368636517 7271385094790059944119347)
                ·
                  refine ⟨10907077642185089916179021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7271385094790059944119347 10907077642185089916179021)
                  ·
                    refine ⟨4090154115819408718567133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10907077642185089916179021 4090154115819408718567133)
                    ·
                      refine ⟨1533807793432278269462675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4090154115819408718567133 1533807793432278269462675)
                      ·
                        rfl

theorem cell23_2987080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_2987080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987080 prefixEnd_2987080 := by exact prefixLift 2987080
  have htrace : WordTrace (prefixWord ++ tailWord_2987080) baseStart_2987080 baseEnd_2987080 := by
    simpa [prefixWord, tailWord_2987080, baseEnd_2987080] using wordTrace_append hprefix tailTrace_2987080
  have hstable : (prefixWord ++ tailWord_2987080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987080).length < 2 ^ (prefixWord ++ tailWord_2987080).sum := by decide
  have hdescent : baseEnd_2987080 < baseStart_2987080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987097 : List Nat := [1, 2, 1, 2, 2, 1, 2, 6, 2, 1, 3]
def baseStart_2987097 : Nat := 118140960795 + 2987097 * 2 ^ 59
def prefixEnd_2987097 : Nat := 4983230072969 + 3 ^ 40 * 2987097 * 2
def baseEnd_2987097 : Nat := 1533816522603404702950097

theorem tailTrace_2987097 : CollatzResearch.WordTrace tailWord_2987097 prefixEnd_2987097 1533816522603404702950097 := by
  unfold tailWord_2987097
  simp only [CollatzResearch.WordTrace]
  refine ⟨108948378059265199397151545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72632252039510132931434363 108948378059265199397151545)
  ·
    refine ⟨81711283544448899547863659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108948378059265199397151545 81711283544448899547863659)
    ·
      refine ⟨122566925316673349321795489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81711283544448899547863659 122566925316673349321795489)
      ·
        refine ⟨91925193987505011991346617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122566925316673349321795489 91925193987505011991346617)
        ·
          refine ⟨68943895490628758993509963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91925193987505011991346617 68943895490628758993509963)
          ·
            refine ⟨103415843235943138490264945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68943895490628758993509963 103415843235943138490264945)
            ·
              refine ⟨77561882426957353867698709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103415843235943138490264945 77561882426957353867698709)
              ·
                refine ⟨3635713238763625962548377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77561882426957353867698709 3635713238763625962548377)
                ·
                  refine ⟨2726784929072719471911283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3635713238763625962548377 2726784929072719471911283)
                  ·
                    refine ⟨4090177393609079207866925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2726784929072719471911283 4090177393609079207866925)
                    ·
                      refine ⟨1533816522603404702950097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4090177393609079207866925 1533816522603404702950097)
                      ·
                        rfl

theorem cell23_2987097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 1, 3].length) (baseStart_2987097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987097 prefixEnd_2987097 := by exact prefixLift 2987097
  have htrace : WordTrace (prefixWord ++ tailWord_2987097) baseStart_2987097 baseEnd_2987097 := by
    simpa [prefixWord, tailWord_2987097, baseEnd_2987097] using wordTrace_append hprefix tailTrace_2987097
  have hstable : (prefixWord ++ tailWord_2987097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987097).length < 2 ^ (prefixWord ++ tailWord_2987097).sum := by decide
  have hdescent : baseEnd_2987097 < baseStart_2987097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987114 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_2987114 : Nat := 118140960795 + 2987114 * 2 ^ 59
def prefixEnd_2987114 : Nat := 4983230072969 + 3 ^ 40 * 2987114 * 2
def baseEnd_2987114 : Nat := 1533825251774531136437519

theorem tailTrace_2987114 : CollatzResearch.WordTrace tailWord_2987114 prefixEnd_2987114 1533825251774531136437519 := by
  unfold tailWord_2987114
  simp only [CollatzResearch.WordTrace]
  refine ⟨27237249525050902825130099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72632665400135740867013597 27237249525050902825130099)
  ·
    refine ⟨40855874287576354237695149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27237249525050902825130099 40855874287576354237695149)
    ·
      refine ⟨15320952857841132839135681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40855874287576354237695149 15320952857841132839135681)
      ·
        refine ⟨11490714643380849629351761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15320952857841132839135681 11490714643380849629351761)
        ·
          refine ⟨8618035982535637222013821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11490714643380849629351761 8618035982535637222013821)
          ·
            refine ⟨3231763493450863958255183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8618035982535637222013821 3231763493450863958255183)
            ·
              refine ⟨4847645240176295937382775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3231763493450863958255183 4847645240176295937382775)
              ·
                refine ⟨7271467860264443906074163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4847645240176295937382775 7271467860264443906074163)
                ·
                  refine ⟨10907201790396665859111245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7271467860264443906074163 10907201790396665859111245)
                  ·
                    refine ⟨4090200671398749697166717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10907201790396665859111245 4090200671398749697166717)
                    ·
                      refine ⟨1533825251774531136437519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4090200671398749697166717 1533825251774531136437519)
                      ·
                        rfl

theorem cell23_2987114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_2987114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987114 prefixEnd_2987114 := by exact prefixLift 2987114
  have htrace : WordTrace (prefixWord ++ tailWord_2987114) baseStart_2987114 baseEnd_2987114 := by
    simpa [prefixWord, tailWord_2987114, baseEnd_2987114] using wordTrace_append hprefix tailTrace_2987114
  have hstable : (prefixWord ++ tailWord_2987114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987114).length < 2 ^ (prefixWord ++ tailWord_2987114).sum := by decide
  have hdescent : baseEnd_2987114 < baseStart_2987114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987123 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 5]
def baseStart_2987123 : Nat := 118140960795 + 2987123 * 2 ^ 59
def prefixEnd_2987123 : Nat := 4983230072969 + 3 ^ 40 * 2987123 * 2
def baseEnd_2987123 : Nat := 1533829873100421601224977

theorem tailTrace_2987123 : CollatzResearch.WordTrace tailWord_2987123 prefixEnd_2987123 1533829873100421601224977 := by
  unfold tailWord_2987123
  simp only [CollatzResearch.WordTrace]
  refine ⟨108949326357171005837598023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72632884238114003891732015 108949326357171005837598023)
  ·
    refine ⟨163423989535756508756397035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108949326357171005837598023 163423989535756508756397035)
    ·
      refine ⟨245135984303634763134595553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163423989535756508756397035 245135984303634763134595553)
      ·
        refine ⟨183851988227726072350946665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245135984303634763134595553 183851988227726072350946665)
        ·
          refine ⟨137888991170794554263209999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183851988227726072350946665 137888991170794554263209999)
          ·
            refine ⟨206833486756191831394814999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137888991170794554263209999 206833486756191831394814999)
            ·
              refine ⟨310250230134287747092222499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206833486756191831394814999 310250230134287747092222499)
              ·
                refine ⟨465375345201431620638333749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310250230134287747092222499 465375345201431620638333749)
                ·
                  refine ⟨43628938612634214434843789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 465375345201431620638333749 43628938612634214434843789)
                  ·
                    refine ⟨16360851979737830413066421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43628938612634214434843789 16360851979737830413066421)
                    ·
                      refine ⟨1533829873100421601224977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16360851979737830413066421 1533829873100421601224977)
                      ·
                        rfl

theorem cell23_2987123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_2987123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987123 prefixEnd_2987123 := by exact prefixLift 2987123
  have htrace : WordTrace (prefixWord ++ tailWord_2987123) baseStart_2987123 baseEnd_2987123 := by
    simpa [prefixWord, tailWord_2987123, baseEnd_2987123] using wordTrace_append hprefix tailTrace_2987123
  have hstable : (prefixWord ++ tailWord_2987123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987123).length < 2 ^ (prefixWord ++ tailWord_2987123).sum := by decide
  have hdescent : baseEnd_2987123 < baseStart_2987123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987140 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_2987140 : Nat := 118140960795 + 2987140 * 2 ^ 59
def prefixEnd_2987140 : Nat := 4983230072969 + 3 ^ 40 * 2987140 * 2
def baseEnd_2987140 : Nat := 1533838602271548034712399

theorem tailTrace_2987140 : CollatzResearch.WordTrace tailWord_2987140 prefixEnd_2987140 1533838602271548034712399 := by
  unfold tailWord_2987140
  simp only [CollatzResearch.WordTrace]
  refine ⟨54474973199054708870483437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72633297598739611827311249 54474973199054708870483437)
  ·
    refine ⟨20428114949645515826431289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54474973199054708870483437 20428114949645515826431289)
    ·
      refine ⟨15321086212234136869823467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20428114949645515826431289 15321086212234136869823467)
      ·
        refine ⟨22981629318351205304735201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15321086212234136869823467 22981629318351205304735201)
        ·
          refine ⟨17236221988763403978551401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22981629318351205304735201 17236221988763403978551401)
          ·
            refine ⟨12927166491572552983913551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17236221988763403978551401 12927166491572552983913551)
            ·
              refine ⟨19390749737358829475870327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12927166491572552983913551 19390749737358829475870327)
              ·
                refine ⟨29086124606038244213805491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19390749737358829475870327 29086124606038244213805491)
                ·
                  refine ⟨43629186909057366320708237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29086124606038244213805491 43629186909057366320708237)
                  ·
                    refine ⟨16360945090896512370265589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43629186909057366320708237 16360945090896512370265589)
                    ·
                      refine ⟨1533838602271548034712399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16360945090896512370265589 1533838602271548034712399)
                      ·
                        rfl

theorem cell23_2987140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_2987140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987140 prefixEnd_2987140 := by exact prefixLift 2987140
  have htrace : WordTrace (prefixWord ++ tailWord_2987140) baseStart_2987140 baseEnd_2987140 := by
    simpa [prefixWord, tailWord_2987140, baseEnd_2987140] using wordTrace_append hprefix tailTrace_2987140
  have hstable : (prefixWord ++ tailWord_2987140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987140).length < 2 ^ (prefixWord ++ tailWord_2987140).sum := by decide
  have hdescent : baseEnd_2987140 < baseStart_2987140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987163 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 8]
def baseStart_2987163 : Nat := 118140960795 + 2987163 * 2 ^ 59
def prefixEnd_2987163 : Nat := 4983230072969 + 3 ^ 40 * 2987163 * 2
def baseEnd_2987163 : Nat := 1533850412326601444724793

theorem tailTrace_2987163 : CollatzResearch.WordTrace tailWord_2987163 prefixEnd_2987163 1533850412326601444724793 := by
  unfold tailWord_2987163
  simp only [CollatzResearch.WordTrace]
  refine ⟨108950785277026092669054143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72633856851350728446036095 108950785277026092669054143)
  ·
    refine ⟨163426177915539139003581215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108950785277026092669054143 163426177915539139003581215)
    ·
      refine ⟨245139266873308708505371823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163426177915539139003581215 245139266873308708505371823)
      ·
        refine ⟨367708900309963062758057735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245139266873308708505371823 367708900309963062758057735)
        ·
          refine ⟨551563350464944594137086603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367708900309963062758057735 551563350464944594137086603)
          ·
            refine ⟨827345025697416891205629905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551563350464944594137086603 827345025697416891205629905)
            ·
              refine ⟨620508769273062668404222429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 827345025697416891205629905 620508769273062668404222429)
              ·
                refine ⟨232690788477398500651583411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 620508769273062668404222429 232690788477398500651583411)
                ·
                  refine ⟨349036182716097750977375117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232690788477398500651583411 349036182716097750977375117)
                  ·
                    refine ⟨130888568518536656616515669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 349036182716097750977375117 130888568518536656616515669)
                    ·
                      refine ⟨1533850412326601444724793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 130888568518536656616515669 1533850412326601444724793)
                      ·
                        rfl

theorem cell23_2987163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 8].length) (baseStart_2987163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987163 prefixEnd_2987163 := by exact prefixLift 2987163
  have htrace : WordTrace (prefixWord ++ tailWord_2987163) baseStart_2987163 baseEnd_2987163 := by
    simpa [prefixWord, tailWord_2987163, baseEnd_2987163] using wordTrace_append hprefix tailTrace_2987163
  have hstable : (prefixWord ++ tailWord_2987163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987163).length < 2 ^ (prefixWord ++ tailWord_2987163).sum := by decide
  have hdescent : baseEnd_2987163 < baseStart_2987163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987244 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 4]
def baseStart_2987244 : Nat := 118140960795 + 2987244 * 2 ^ 59
def prefixEnd_2987244 : Nat := 4983230072969 + 3 ^ 40 * 2987244 * 2
def baseEnd_2987244 : Nat := 1533892004259615627811921

theorem tailTrace_2987244 : CollatzResearch.WordTrace tailWord_2987244 prefixEnd_2987244 1533892004259615627811921 := by
  unfold tailWord_2987244
  simp only [CollatzResearch.WordTrace]
  refine ⟨54476869794866321751376393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72635826393155095668501857 54476869794866321751376393)
  ·
    refine ⟨40857652346149741313532295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54476869794866321751376393 40857652346149741313532295)
    ·
      refine ⟨61286478519224611970298443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40857652346149741313532295 61286478519224611970298443)
      ·
        refine ⟨91929717778836917955447665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61286478519224611970298443 91929717778836917955447665)
        ·
          refine ⟨68947288334127688466585749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91929717778836917955447665 68947288334127688466585749)
          ·
            refine ⟨3231904140662235396871207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68947288334127688466585749 3231904140662235396871207)
            ·
              refine ⟨4847856210993353095306811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3231904140662235396871207 4847856210993353095306811)
              ·
                refine ⟨7271784316490029642960217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4847856210993353095306811 7271784316490029642960217)
                ·
                  refine ⟨5453838237367522232220163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7271784316490029642960217 5453838237367522232220163)
                  ·
                    refine ⟨8180757356051283348330245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5453838237367522232220163 8180757356051283348330245)
                    ·
                      refine ⟨1533892004259615627811921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8180757356051283348330245 1533892004259615627811921)
                      ·
                        rfl

theorem cell23_2987244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_2987244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987244 prefixEnd_2987244 := by exact prefixLift 2987244
  have htrace : WordTrace (prefixWord ++ tailWord_2987244) baseStart_2987244 baseEnd_2987244 := by
    simpa [prefixWord, tailWord_2987244, baseEnd_2987244] using wordTrace_append hprefix tailTrace_2987244
  have hstable : (prefixWord ++ tailWord_2987244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987244).length < 2 ^ (prefixWord ++ tailWord_2987244).sum := by decide
  have hdescent : baseEnd_2987244 < baseStart_2987244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987267 : List Nat := [1, 1, 1, 3, 2, 4, 3, 2, 6]
def baseStart_2987267 : Nat := 118140960795 + 2987267 * 2 ^ 59
def prefixEnd_2987267 : Nat := 4983230072969 + 3 ^ 40 * 2987267 * 2
def baseEnd_2987267 : Nat := 170433757146074337536035

theorem tailTrace_2987267 : CollatzResearch.WordTrace tailWord_2987267 prefixEnd_2987267 170433757146074337536035 := by
  unfold tailWord_2987267
  simp only [CollatzResearch.WordTrace]
  refine ⟨108954578468649318430840055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72636385645766212287226703 108954578468649318430840055)
  ·
    refine ⟨163431867702973977646260083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108954578468649318430840055 163431867702973977646260083)
    ·
      refine ⟨245147801554460966469390125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163431867702973977646260083 245147801554460966469390125)
      ·
        refine ⟨91930425582922862426021297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245147801554460966469390125 91930425582922862426021297)
        ·
          refine ⟨68947819187192146819515973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91930425582922862426021297 68947819187192146819515973)
          ·
            refine ⟨12927716097598527528659245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68947819187192146819515973 12927716097598527528659245)
            ·
              refine ⟨4847893536599447823247217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12927716097598527528659245 4847893536599447823247217)
              ·
                refine ⟨3635920152449585867435413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4847893536599447823247217 3635920152449585867435413)
                ·
                  refine ⟨170433757146074337536035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3635920152449585867435413 170433757146074337536035)
                  ·
                    rfl

theorem cell23_2987267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 6].length) (baseStart_2987267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987267 prefixEnd_2987267 := by exact prefixLift 2987267
  have htrace : WordTrace (prefixWord ++ tailWord_2987267) baseStart_2987267 baseEnd_2987267 := by
    simpa [prefixWord, tailWord_2987267, baseEnd_2987267] using wordTrace_append hprefix tailTrace_2987267
  have hstable : (prefixWord ++ tailWord_2987267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987267).length < 2 ^ (prefixWord ++ tailWord_2987267).sum := by decide
  have hdescent : baseEnd_2987267 < baseStart_2987267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987314 : List Nat := [3, 2, 1, 1, 4, 1, 2, 3, 1, 5]
def baseStart_2987314 : Nat := 118140960795 + 2987314 * 2 ^ 59
def prefixEnd_2987314 : Nat := 4983230072969 + 3 ^ 40 * 2987314 * 2
def baseEnd_2987314 : Nat := 511309315968476784645533

theorem tailTrace_2987314 : CollatzResearch.WordTrace tailWord_2987314 prefixEnd_2987314 511309315968476784645533 := by
  unfold tailWord_2987314
  simp only [CollatzResearch.WordTrace]
  refine ⟨27239073174869761364450249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72637528466319363638533997 27239073174869761364450249)
  ·
    refine ⟨20429304881152321023337687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27239073174869761364450249 20429304881152321023337687)
    ·
      refine ⟨30643957321728481535006531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20429304881152321023337687 30643957321728481535006531)
      ·
        refine ⟨45965935982592722302509797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30643957321728481535006531 45965935982592722302509797)
        ·
          refine ⟨8618612996736135431720587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45965935982592722302509797 8618612996736135431720587)
          ·
            refine ⟨12927919495104203147580881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8618612996736135431720587 12927919495104203147580881)
            ·
              refine ⟨9695939621328152360685661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12927919495104203147580881 9695939621328152360685661)
              ·
                refine ⟨3635977357998057135257123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9695939621328152360685661 3635977357998057135257123)
                ·
                  refine ⟨5453966036997085702885685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3635977357998057135257123 5453966036997085702885685)
                  ·
                    refine ⟨511309315968476784645533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5453966036997085702885685 511309315968476784645533)
                    ·
                      rfl

theorem cell23_2987314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_2987314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987314 prefixEnd_2987314 := by exact prefixLift 2987314
  have htrace : WordTrace (prefixWord ++ tailWord_2987314) baseStart_2987314 baseEnd_2987314 := by
    simpa [prefixWord, tailWord_2987314, baseEnd_2987314] using wordTrace_append hprefix tailTrace_2987314
  have hstable : (prefixWord ++ tailWord_2987314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987314).length < 2 ^ (prefixWord ++ tailWord_2987314).sum := by decide
  have hdescent : baseEnd_2987314 < baseStart_2987314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987328 : List Nat := [2, 1, 1, 2, 2, 1, 7, 2, 1, 1, 3]
def baseStart_2987328 : Nat := 118140960795 + 2987328 * 2 ^ 59
def prefixEnd_2987328 : Nat := 4983230072969 + 3 ^ 40 * 2987328 * 2
def baseEnd_2987328 : Nat := 1533935136634593299161535

theorem tailTrace_2987328 : CollatzResearch.WordTrace tailWord_2987328 prefixEnd_2987328 1533935136634593299161535 := by
  unfold tailWord_2987328
  simp only [CollatzResearch.WordTrace]
  refine ⟨54478401660714162924405319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72637868880952217232540425 54478401660714162924405319)
  ·
    refine ⟨81717602491071244386607979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54478401660714162924405319 81717602491071244386607979)
    ·
      refine ⟨122576403736606866579911969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81717602491071244386607979 122576403736606866579911969)
      ·
        refine ⟨91932302802455149934933977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122576403736606866579911969 91932302802455149934933977)
        ·
          refine ⟨68949227101841362451200483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91932302802455149934933977 68949227101841362451200483)
          ·
            refine ⟨103423840652762043676800725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68949227101841362451200483 103423840652762043676800725)
            ·
              refine ⟨2423996265299110398675017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 103423840652762043676800725 2423996265299110398675017)
              ·
                refine ⟨1817997198974332799006263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2423996265299110398675017 1817997198974332799006263)
                ·
                  refine ⟨2726995798461499198509395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817997198974332799006263 2726995798461499198509395)
                  ·
                    refine ⟨4090493697692248797764093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2726995798461499198509395 4090493697692248797764093)
                    ·
                      refine ⟨1533935136634593299161535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4090493697692248797764093 1533935136634593299161535)
                      ·
                        rfl

theorem cell23_2987328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 1, 1, 3].length) (baseStart_2987328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987328 prefixEnd_2987328 := by exact prefixLift 2987328
  have htrace : WordTrace (prefixWord ++ tailWord_2987328) baseStart_2987328 baseEnd_2987328 := by
    simpa [prefixWord, tailWord_2987328, baseEnd_2987328] using wordTrace_append hprefix tailTrace_2987328
  have hstable : (prefixWord ++ tailWord_2987328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987328).length < 2 ^ (prefixWord ++ tailWord_2987328).sum := by decide
  have hdescent : baseEnd_2987328 < baseStart_2987328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987337 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 1, 1, 5]
def baseStart_2987337 : Nat := 118140960795 + 2987337 * 2 ^ 59
def prefixEnd_2987337 : Nat := 4983230072969 + 3 ^ 40 * 2987337 * 2
def baseEnd_2987337 : Nat := 1533939757960483763948993

theorem tailTrace_2987337 : CollatzResearch.WordTrace tailWord_2987337 prefixEnd_2987337 1533939757960483763948993 := by
  unfold tailWord_2987337
  simp only [CollatzResearch.WordTrace]
  refine ⟨108957131578395720385888265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72638087718930480257258843 108957131578395720385888265)
  ·
    refine ⟨81717848683796790289416199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108957131578395720385888265 81717848683796790289416199)
    ·
      refine ⟨122576773025695185434124299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81717848683796790289416199 122576773025695185434124299)
      ·
        refine ⟨183865159538542778151186449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122576773025695185434124299 183865159538542778151186449)
        ·
          refine ⟨137898869653907083613389837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183865159538542778151186449 137898869653907083613389837)
          ·
            refine ⟨51712076120215156355021189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137898869653907083613389837 51712076120215156355021189)
            ·
              refine ⟨9696014272540341816566473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51712076120215156355021189 9696014272540341816566473)
              ·
                refine ⟨7272010704405256362424855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9696014272540341816566473 7272010704405256362424855)
                ·
                  refine ⟨10908016056607884543637283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7272010704405256362424855 10908016056607884543637283)
                  ·
                    refine ⟨16362024084911826815455925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10908016056607884543637283 16362024084911826815455925)
                    ·
                      refine ⟨1533939757960483763948993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16362024084911826815455925 1533939757960483763948993)
                      ·
                        rfl

theorem cell23_2987337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 1, 5].length) (baseStart_2987337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987337 prefixEnd_2987337 := by exact prefixLift 2987337
  have htrace : WordTrace (prefixWord ++ tailWord_2987337) baseStart_2987337 baseEnd_2987337 := by
    simpa [prefixWord, tailWord_2987337, baseEnd_2987337] using wordTrace_append hprefix tailTrace_2987337
  have hstable : (prefixWord ++ tailWord_2987337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987337).length < 2 ^ (prefixWord ++ tailWord_2987337).sum := by decide
  have hdescent : baseEnd_2987337 < baseStart_2987337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987344 : List Nat := [2, 1, 1, 1, 1, 5, 3, 3, 2, 4]
def baseStart_2987344 : Nat := 118140960795 + 2987344 * 2 ^ 59
def prefixEnd_2987344 : Nat := 4983230072969 + 3 ^ 40 * 2987344 * 2
def baseEnd_2987344 : Nat := 511314450775021745520487

theorem tailTrace_2987344 : CollatzResearch.WordTrace tailWord_2987344 prefixEnd_2987344 511314450775021745520487 := by
  unfold tailWord_2987344
  simp only [CollatzResearch.WordTrace]
  refine ⟨54478693444685180290696543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72638257926246907054262057 54478693444685180290696543)
  ·
    refine ⟨81718040167027770436044815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54478693444685180290696543 81718040167027770436044815)
    ·
      refine ⟨122577060250541655654067223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81718040167027770436044815 122577060250541655654067223)
      ·
        refine ⟨183865590375812483481100835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122577060250541655654067223 183865590375812483481100835)
        ·
          refine ⟨275798385563718725221651253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183865590375812483481100835 275798385563718725221651253)
          ·
            refine ⟨25856098646598630489529805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 275798385563718725221651253 25856098646598630489529805)
            ·
              refine ⟨9696036992474486433573677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25856098646598630489529805 9696036992474486433573677)
              ·
                refine ⟨3636013872177932412590129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9696036992474486433573677 3636013872177932412590129)
                ·
                  refine ⟨2727010404133449309442597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3636013872177932412590129 2727010404133449309442597)
                  ·
                    refine ⟨511314450775021745520487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2727010404133449309442597 511314450775021745520487)
                    ·
                      rfl

theorem cell23_2987344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 2, 4].length) (baseStart_2987344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987344 prefixEnd_2987344 := by exact prefixLift 2987344
  have htrace : WordTrace (prefixWord ++ tailWord_2987344) baseStart_2987344 baseEnd_2987344 := by
    simpa [prefixWord, tailWord_2987344, baseEnd_2987344] using wordTrace_append hprefix tailTrace_2987344
  have hstable : (prefixWord ++ tailWord_2987344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987344).length < 2 ^ (prefixWord ++ tailWord_2987344).sum := by decide
  have hdescent : baseEnd_2987344 < baseStart_2987344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987347 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 4]
def baseStart_2987347 : Nat := 118140960795 + 2987347 * 2 ^ 59
def prefixEnd_2987347 : Nat := 4983230072969 + 3 ^ 40 * 2987347 * 2
def baseEnd_2987347 : Nat := 1533944892767028724823947

theorem tailTrace_2987347 : CollatzResearch.WordTrace tailWord_2987347 prefixEnd_2987347 1533944892767028724823947 := by
  unfold tailWord_2987347
  simp only [CollatzResearch.WordTrace]
  refine ⟨108957496308359492093752295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72638330872239661395834863 108957496308359492093752295)
  ·
    refine ⟨163436244462539238140628443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108957496308359492093752295 163436244462539238140628443)
    ·
      refine ⟨245154366693808857210942665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163436244462539238140628443 245154366693808857210942665)
      ·
        refine ⟨183865775020356642908206999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245154366693808857210942665 183865775020356642908206999)
        ·
          refine ⟨275798662530534964362310499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183865775020356642908206999 275798662530534964362310499)
          ·
            refine ⟨413697993795802446543465749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275798662530534964362310499 413697993795802446543465749)
            ·
              refine ⟨19392093459178239681724957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 413697993795802446543465749 19392093459178239681724957)
              ·
                refine ⟨7272035047191839880646859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19392093459178239681724957 7272035047191839880646859)
                ·
                  refine ⟨10908052570787759820970289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7272035047191839880646859 10908052570787759820970289)
                  ·
                    refine ⟨8181039428090819865727717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10908052570787759820970289 8181039428090819865727717)
                    ·
                      refine ⟨1533944892767028724823947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8181039428090819865727717 1533944892767028724823947)
                      ·
                        rfl

theorem cell23_2987347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 4].length) (baseStart_2987347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987347 prefixEnd_2987347 := by exact prefixLift 2987347
  have htrace : WordTrace (prefixWord ++ tailWord_2987347) baseStart_2987347 baseEnd_2987347 := by
    simpa [prefixWord, tailWord_2987347, baseEnd_2987347] using wordTrace_append hprefix tailTrace_2987347
  have hstable : (prefixWord ++ tailWord_2987347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987347).length < 2 ^ (prefixWord ++ tailWord_2987347).sum := by decide
  have hdescent : baseEnd_2987347 < baseStart_2987347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987351 : List Nat := [1, 1, 3, 2, 3, 4, 1, 2, 1, 1, 4]
def baseStart_2987351 : Nat := 118140960795 + 2987351 * 2 ^ 59
def prefixEnd_2987351 : Nat := 4983230072969 + 3 ^ 40 * 2987351 * 2
def baseEnd_2987351 : Nat := 1533946946689646709173929

theorem tailTrace_2987351 : CollatzResearch.WordTrace tailWord_2987351 prefixEnd_2987351 1533946946689646709173929 := by
  unfold tailWord_2987351
  simp only [CollatzResearch.WordTrace]
  refine ⟨108957642200345000776897907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72638428133563333851265271 108957642200345000776897907)
  ·
    refine ⟨163436463300517501165346861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108957642200345000776897907 163436463300517501165346861)
    ·
      refine ⟨61288673737694062937005073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163436463300517501165346861 61288673737694062937005073)
      ·
        refine ⟨45966505303270547202753805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61288673737694062937005073 45966505303270547202753805)
        ·
          refine ⟨17237439488726455201032677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45966505303270547202753805 17237439488726455201032677)
          ·
            refine ⟨3232019904136210350193627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17237439488726455201032677 3232019904136210350193627)
            ·
              refine ⟨4848029856204315525290441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3232019904136210350193627 4848029856204315525290441)
              ·
                refine ⟨3636022392153236643967831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4848029856204315525290441 3636022392153236643967831)
                ·
                  refine ⟨5454033588229854965951747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3636022392153236643967831 5454033588229854965951747)
                  ·
                    refine ⟨8181050382344782448927621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5454033588229854965951747 8181050382344782448927621)
                    ·
                      refine ⟨1533946946689646709173929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8181050382344782448927621 1533946946689646709173929)
                      ·
                        rfl

theorem cell23_2987351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_2987351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987351 prefixEnd_2987351 := by exact prefixLift 2987351
  have htrace : WordTrace (prefixWord ++ tailWord_2987351) baseStart_2987351 baseEnd_2987351 := by
    simpa [prefixWord, tailWord_2987351, baseEnd_2987351] using wordTrace_append hprefix tailTrace_2987351
  have hstable : (prefixWord ++ tailWord_2987351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987351).length < 2 ^ (prefixWord ++ tailWord_2987351).sum := by decide
  have hdescent : baseEnd_2987351 < baseStart_2987351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987364 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_2987364 : Nat := 118140960795 + 2987364 * 2 ^ 59
def prefixEnd_2987364 : Nat := 4983230072969 + 3 ^ 40 * 2987364 * 2
def baseEnd_2987364 : Nat := 1533953621938155158311369

theorem tailTrace_2987364 : CollatzResearch.WordTrace tailWord_2987364 prefixEnd_2987364 1533953621938155158311369 := by
  unfold tailWord_2987364
  simp only [CollatzResearch.WordTrace]
  refine ⟨54479058174648951998560573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72638744232865269331414097 54479058174648951998560573)
  ·
    refine ⟨20429646815493356999460215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54479058174648951998560573 20429646815493356999460215)
    ·
      refine ⟨30644470223240035499190323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20429646815493356999460215 30644470223240035499190323)
      ·
        refine ⟨45966705334860053248785485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30644470223240035499190323 45966705334860053248785485)
        ·
          refine ⟨17237514500572519968294557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45966705334860053248785485 17237514500572519968294557)
          ·
            refine ⟨6464067937714694988110459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17237514500572519968294557 6464067937714694988110459)
            ·
              refine ⟨9696101906572042482165689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6464067937714694988110459 9696101906572042482165689)
              ·
                refine ⟨7272076429929031861624267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9696101906572042482165689 7272076429929031861624267)
                ·
                  refine ⟨10908114644893547792436401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7272076429929031861624267 10908114644893547792436401)
                  ·
                    refine ⟨8181085983670160844327301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10908114644893547792436401 8181085983670160844327301)
                    ·
                      refine ⟨1533953621938155158311369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8181085983670160844327301 1533953621938155158311369)
                      ·
                        rfl

theorem cell23_2987364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_2987364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987364 prefixEnd_2987364 := by exact prefixLift 2987364
  have htrace : WordTrace (prefixWord ++ tailWord_2987364) baseStart_2987364 baseEnd_2987364 := by
    simpa [prefixWord, tailWord_2987364, baseEnd_2987364] using wordTrace_append hprefix tailTrace_2987364
  have hstable : (prefixWord ++ tailWord_2987364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987364).length < 2 ^ (prefixWord ++ tailWord_2987364).sum := by decide
  have hdescent : baseEnd_2987364 < baseStart_2987364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987368 : List Nat := [2, 1, 4, 2, 3, 1, 3, 1, 1, 1, 4]
def baseStart_2987368 : Nat := 118140960795 + 2987368 * 2 ^ 59
def prefixEnd_2987368 : Nat := 4983230072969 + 3 ^ 40 * 2987368 * 2
def baseEnd_2987368 : Nat := 1533955675860773142661351

theorem tailTrace_2987368 : CollatzResearch.WordTrace tailWord_2987368 prefixEnd_2987368 1533955675860773142661351 := by
  unfold tailWord_2987368
  simp only [CollatzResearch.WordTrace]
  refine ⟨54479131120641706340133379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72638841494188941786844505 54479131120641706340133379)
  ·
    refine ⟨81718696680962559510200069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54479131120641706340133379 81718696680962559510200069)
    ·
      refine ⟨15322255627680479908162513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81718696680962559510200069 15322255627680479908162513)
      ·
        refine ⟨11491691720760359931121885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15322255627680479908162513 11491691720760359931121885)
        ·
          refine ⟨4309384395285134974170707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11491691720760359931121885 4309384395285134974170707)
          ·
            refine ⟨6464076592927702461256061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4309384395285134974170707 6464076592927702461256061)
            ·
              refine ⟨2424028722347888422971023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6464076592927702461256061 2424028722347888422971023)
              ·
                refine ⟨3636043083521832634456535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2424028722347888422971023 3636043083521832634456535)
                ·
                  refine ⟨5454064625282748951684803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3636043083521832634456535 5454064625282748951684803)
                  ·
                    refine ⟨8181096937924123427527205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5454064625282748951684803 8181096937924123427527205)
                    ·
                      refine ⟨1533955675860773142661351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8181096937924123427527205 1533955675860773142661351)
                      ·
                        rfl

theorem cell23_2987368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_2987368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987368 prefixEnd_2987368 := by exact prefixLift 2987368
  have htrace : WordTrace (prefixWord ++ tailWord_2987368) baseStart_2987368 baseEnd_2987368 := by
    simpa [prefixWord, tailWord_2987368, baseEnd_2987368] using wordTrace_append hprefix tailTrace_2987368
  have hstable : (prefixWord ++ tailWord_2987368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987368).length < 2 ^ (prefixWord ++ tailWord_2987368).sum := by decide
  have hdescent : baseEnd_2987368 < baseStart_2987368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987374 : List Nat := [4, 1, 2, 4, 1, 11]
def baseStart_2987374 : Nat := 118140960795 + 2987374 * 2 ^ 59
def prefixEnd_2987374 : Nat := 4983230072969 + 3 ^ 40 * 2987374 * 2
def baseEnd_2987374 : Nat := 6312587476315638350561

theorem tailTrace_2987374 : CollatzResearch.WordTrace tailWord_2987374 prefixEnd_2987374 6312587476315638350561 := by
  unfold tailWord_2987374
  simp only [CollatzResearch.WordTrace]
  refine ⟨13619810134907709463123147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72638987386174450469990117 13619810134907709463123147)
  ·
    refine ⟨20429715202361564194684721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13619810134907709463123147 20429715202361564194684721)
    ·
      refine ⟨15322286401771173146013541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20429715202361564194684721 15322286401771173146013541)
      ·
        refine ⟨2872928700332094964877539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15322286401771173146013541 2872928700332094964877539)
        ·
          refine ⟨4309393050498142447316309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2872928700332094964877539 4309393050498142447316309)
          ·
            refine ⟨6312587476315638350561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4309393050498142447316309 6312587476315638350561)
            ·
              rfl

theorem cell23_2987374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 11].length) (baseStart_2987374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987374 prefixEnd_2987374 := by exact prefixLift 2987374
  have htrace : WordTrace (prefixWord ++ tailWord_2987374) baseStart_2987374 baseEnd_2987374 := by
    simpa [prefixWord, tailWord_2987374, baseEnd_2987374] using wordTrace_append hprefix tailTrace_2987374
  have hstable : (prefixWord ++ tailWord_2987374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987374).length < 2 ^ (prefixWord ++ tailWord_2987374).sum := by decide
  have hdescent : baseEnd_2987374 < baseStart_2987374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987385 : List Nat := [1, 2, 1, 3, 2, 1, 6, 2, 1, 2, 2]
def baseStart_2987385 : Nat := 118140960795 + 2987385 * 2 ^ 59
def prefixEnd_2987385 : Nat := 4983230072969 + 3 ^ 40 * 2987385 * 2
def baseEnd_2987385 : Nat := 1533964405031899576148773

theorem tailTrace_2987385 : CollatzResearch.WordTrace tailWord_2987385 prefixEnd_2987385 1533964405031899576148773 := by
  unfold tailWord_2987385
  simp only [CollatzResearch.WordTrace]
  refine ⟨108958882282221824583635609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72639254854814549722423739 108958882282221824583635609)
  ·
    refine ⟨81719161711666368437726707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108958882282221824583635609 81719161711666368437726707)
    ·
      refine ⟨122578742567499552656590061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81719161711666368437726707 122578742567499552656590061)
      ·
        refine ⟨45967028462812332246221273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122578742567499552656590061 45967028462812332246221273)
        ·
          refine ⟨34475271347109249184665955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45967028462812332246221273 34475271347109249184665955)
          ·
            refine ⟨51712907020663873776998933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34475271347109249184665955 51712907020663873776998933)
            ·
              refine ⟨2424042516593619083296825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51712907020663873776998933 2424042516593619083296825)
              ·
                refine ⟨1818031887445214312472619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2424042516593619083296825 1818031887445214312472619)
                ·
                  refine ⟨2727047831167821468708929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1818031887445214312472619 2727047831167821468708929)
                  ·
                    refine ⟨2045285873375866101531697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2727047831167821468708929 2045285873375866101531697)
                    ·
                      refine ⟨1533964405031899576148773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2045285873375866101531697 1533964405031899576148773)
                      ·
                        rfl

theorem cell23_2987385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_2987385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987385 prefixEnd_2987385 := by exact prefixLift 2987385
  have htrace : WordTrace (prefixWord ++ tailWord_2987385) baseStart_2987385 baseEnd_2987385 := by
    simpa [prefixWord, tailWord_2987385, baseEnd_2987385] using wordTrace_append hprefix tailTrace_2987385
  have hstable : (prefixWord ++ tailWord_2987385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987385).length < 2 ^ (prefixWord ++ tailWord_2987385).sum := by decide
  have hdescent : baseEnd_2987385 < baseStart_2987385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987401 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 1, 3, 3]
def baseStart_2987401 : Nat := 118140960795 + 2987401 * 2 ^ 59
def prefixEnd_2987401 : Nat := 4983230072969 + 3 ^ 40 * 2987401 * 2
def baseEnd_2987401 : Nat := 1533972620722371513548699

theorem tailTrace_2987401 : CollatzResearch.WordTrace tailWord_2987401 prefixEnd_2987401 1533972620722371513548699 := by
  unfold tailWord_2987401
  simp only [CollatzResearch.WordTrace]
  refine ⟨108959465850163859316218057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72639643900109239544145371 108959465850163859316218057)
  ·
    refine ⟨81719599387622894487163543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108959465850163859316218057 81719599387622894487163543)
    ·
      refine ⟨122579399081434341730745315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81719599387622894487163543 122579399081434341730745315)
      ·
        refine ⟨183869098622151512596117973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122579399081434341730745315 183869098622151512596117973)
        ·
          refine ⟨4309431998956676076471515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 183869098622151512596117973 4309431998956676076471515)
          ·
            refine ⟨6464147998435014114707273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4309431998956676076471515 6464147998435014114707273)
            ·
              refine ⟨4848110998826260586030455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6464147998435014114707273 4848110998826260586030455)
              ·
                refine ⟨7272166498239390879045683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4848110998826260586030455 7272166498239390879045683)
                ·
                  refine ⟨10908249747359086318568525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7272166498239390879045683 10908249747359086318568525)
                  ·
                    refine ⟨4090593655259657369463197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10908249747359086318568525 4090593655259657369463197)
                    ·
                      refine ⟨1533972620722371513548699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4090593655259657369463197 1533972620722371513548699)
                      ·
                        rfl

theorem cell23_2987401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 3, 3].length) (baseStart_2987401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987401 prefixEnd_2987401 := by exact prefixLift 2987401
  have htrace : WordTrace (prefixWord ++ tailWord_2987401) baseStart_2987401 baseEnd_2987401 := by
    simpa [prefixWord, tailWord_2987401, baseEnd_2987401] using wordTrace_append hprefix tailTrace_2987401
  have hstable : (prefixWord ++ tailWord_2987401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987401).length < 2 ^ (prefixWord ++ tailWord_2987401).sum := by decide
  have hdescent : baseEnd_2987401 < baseStart_2987401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987422 : List Nat := [4, 3, 1, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_2987422 : Nat := 118140960795 + 2987422 * 2 ^ 59
def prefixEnd_2987422 : Nat := 4983230072969 + 3 ^ 40 * 2987422 * 2
def baseEnd_2987422 : Nat := 1533983403816115931386103

theorem tailTrace_2987422 : CollatzResearch.WordTrace tailWord_2987422 prefixEnd_2987422 1533983403816115931386103 := by
  unfold tailWord_2987422
  simp only [CollatzResearch.WordTrace]
  refine ⟨13620028972885972487841565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72640154522058519935155013 13620028972885972487841565)
  ·
    refine ⟨5107510864832239682940587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13620028972885972487841565 5107510864832239682940587)
    ·
      refine ⟨7661266297248359524410881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5107510864832239682940587 7661266297248359524410881)
      ·
        refine ⟨5745949722936269643308161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7661266297248359524410881 5745949722936269643308161)
        ·
          refine ⟨4309462292202202232481121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5745949722936269643308161 4309462292202202232481121)
          ·
            refine ⟨3232096719151651674360841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4309462292202202232481121 3232096719151651674360841)
            ·
              refine ⟨2424072539363738755770631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3232096719151651674360841 2424072539363738755770631)
              ·
                refine ⟨3636108809045608133655947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2424072539363738755770631 3636108809045608133655947)
                ·
                  refine ⟨5454163213568412200483921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3636108809045608133655947 5454163213568412200483921)
                  ·
                    refine ⟨4090622410176309150362941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5454163213568412200483921 4090622410176309150362941)
                    ·
                      refine ⟨1533983403816115931386103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4090622410176309150362941 1533983403816115931386103)
                      ·
                        rfl

theorem cell23_2987422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_2987422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987422 prefixEnd_2987422 := by exact prefixLift 2987422
  have htrace : WordTrace (prefixWord ++ tailWord_2987422) baseStart_2987422 baseEnd_2987422 := by
    simpa [prefixWord, tailWord_2987422, baseEnd_2987422] using wordTrace_append hprefix tailTrace_2987422
  have hstable : (prefixWord ++ tailWord_2987422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987422).length < 2 ^ (prefixWord ++ tailWord_2987422).sum := by decide
  have hdescent : baseEnd_2987422 < baseStart_2987422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987427 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 5]
def baseStart_2987427 : Nat := 118140960795 + 2987427 * 2 ^ 59
def prefixEnd_2987427 : Nat := 4983230072969 + 3 ^ 40 * 2987427 * 2
def baseEnd_2987427 : Nat := 1533985971219388411823579

theorem tailTrace_2987427 : CollatzResearch.WordTrace tailWord_2987427 prefixEnd_2987427 1533985971219388411823579 := by
  unfold tailWord_2987427
  simp only [CollatzResearch.WordTrace]
  refine ⟨108960414148069665756664535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72640276098713110504443023 108960414148069665756664535)
  ·
    refine ⟨163440621222104498634996803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108960414148069665756664535 163440621222104498634996803)
    ·
      refine ⟨245160931833156747952495205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163440621222104498634996803 245160931833156747952495205)
      ·
        refine ⟨45967674718716890241092851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245160931833156747952495205 45967674718716890241092851)
        ·
          refine ⟨68951512078075335361639277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45967674718716890241092851 68951512078075335361639277)
          ·
            refine ⟨25856817029278250760614729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68951512078075335361639277 25856817029278250760614729)
            ·
              refine ⟨19392612771958688070461047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25856817029278250760614729 19392612771958688070461047)
              ·
                refine ⟨29088919157938032105691571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19392612771958688070461047 29088919157938032105691571)
                ·
                  refine ⟨43633378736907048158537357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29088919157938032105691571 43633378736907048158537357)
                  ·
                    refine ⟨16362517026340143059451509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43633378736907048158537357 16362517026340143059451509)
                    ·
                      refine ⟨1533985971219388411823579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16362517026340143059451509 1533985971219388411823579)
                      ·
                        rfl

theorem cell23_2987427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_2987427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987427 prefixEnd_2987427 := by exact prefixLift 2987427
  have htrace : WordTrace (prefixWord ++ tailWord_2987427) baseStart_2987427 baseEnd_2987427 := by
    simpa [prefixWord, tailWord_2987427, baseEnd_2987427] using wordTrace_append hprefix tailTrace_2987427
  have hstable : (prefixWord ++ tailWord_2987427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987427).length < 2 ^ (prefixWord ++ tailWord_2987427).sum := by decide
  have hdescent : baseEnd_2987427 < baseStart_2987427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987481 : List Nat := [1, 2, 1, 2, 4, 2, 3, 3, 5]
def baseStart_2987481 : Nat := 118140960795 + 2987481 * 2 ^ 59
def prefixEnd_2987481 : Nat := 4983230072969 + 3 ^ 40 * 2987481 * 2
def baseEnd_2987481 : Nat := 170445966574970133394259

theorem tailTrace_2987481 : CollatzResearch.WordTrace tailWord_2987481 prefixEnd_2987481 170445966574970133394259 := by
  unfold tailWord_2987481
  simp only [CollatzResearch.WordTrace]
  refine ⟨108962383689874032979130297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72641589126582688652753531 108962383689874032979130297)
  ·
    refine ⟨81721787767405524734347723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108962383689874032979130297 81721787767405524734347723)
    ·
      refine ⟨122582681651108287101521585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81721787767405524734347723 122582681651108287101521585)
      ·
        refine ⟨91937011238331215326141189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122582681651108287101521585 91937011238331215326141189)
        ·
          refine ⟨17238189607187102873651473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91937011238331215326141189 17238189607187102873651473)
          ·
            refine ⟨12928642205390327155238605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17238189607187102873651473 12928642205390327155238605)
            ·
              refine ⟨4848240827021372683214477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12928642205390327155238605 4848240827021372683214477)
              ·
                refine ⟨1818090310133014756205429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4848240827021372683214477 1818090310133014756205429)
                ·
                  refine ⟨170445966574970133394259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1818090310133014756205429 170445966574970133394259)
                  ·
                    rfl

theorem cell23_2987481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 5].length) (baseStart_2987481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987481 prefixEnd_2987481 := by exact prefixLift 2987481
  have htrace : WordTrace (prefixWord ++ tailWord_2987481) baseStart_2987481 baseEnd_2987481 := by
    simpa [prefixWord, tailWord_2987481, baseEnd_2987481] using wordTrace_append hprefix tailTrace_2987481
  have hstable : (prefixWord ++ tailWord_2987481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987481).length < 2 ^ (prefixWord ++ tailWord_2987481).sum := by decide
  have hdescent : baseEnd_2987481 < baseStart_2987481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987498 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 7]
def baseStart_2987498 : Nat := 118140960795 + 2987498 * 2 ^ 59
def prefixEnd_2987498 : Nat := 4983230072969 + 3 ^ 40 * 2987498 * 2
def baseEnd_2987498 : Nat := 170446936482873070448417

theorem tailTrace_2987498 : CollatzResearch.WordTrace tailWord_2987498 prefixEnd_2987498 170446936482873070448417 := by
  unfold tailWord_2987498
  simp only [CollatzResearch.WordTrace]
  refine ⟨27240750932703111220624787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72642002487208296588332765 27240750932703111220624787)
  ·
    refine ⟨40861126399054666830937181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27240750932703111220624787 40861126399054666830937181)
    ·
      refine ⟨15322922399645500061601443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40861126399054666830937181 15322922399645500061601443)
      ·
        refine ⟨22984383599468250092402165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15322922399645500061601443 22984383599468250092402165)
        ·
          refine ⟨2154785962450148446162703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22984383599468250092402165 2154785962450148446162703)
          ·
            refine ⟨3232178943675222669244055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2154785962450148446162703 3232178943675222669244055)
            ·
              refine ⟨4848268415512834003866083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3232178943675222669244055 4848268415512834003866083)
              ·
                refine ⟨7272402623269251005799125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4848268415512834003866083 7272402623269251005799125)
                ·
                  refine ⟨170446936482873070448417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7272402623269251005799125 170446936482873070448417)
                  ·
                    rfl

theorem cell23_2987498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 7].length) (baseStart_2987498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987498 prefixEnd_2987498 := by exact prefixLift 2987498
  have htrace : WordTrace (prefixWord ++ tailWord_2987498) baseStart_2987498 baseEnd_2987498 := by
    simpa [prefixWord, tailWord_2987498, baseEnd_2987498] using wordTrace_append hprefix tailTrace_2987498
  have hstable : (prefixWord ++ tailWord_2987498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987498).length < 2 ^ (prefixWord ++ tailWord_2987498).sum := by decide
  have hdescent : baseEnd_2987498 < baseStart_2987498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
